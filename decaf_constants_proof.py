#!/usr/bin/env python3
"""Kernel-check shared Decaf field constants and explicit primality certificates."""
import json
import os
import re
from pathlib import Path
import shutil
import tempfile

import formal
from decaf_fiat_proof import validate_proof_build
from decaf_go_proof import validate_assumptions
from decaf_inventory import atomic_json
from security import bounded_run

ROOTS = tuple("FieldConstants." + name for name in
              ("fq_prime", "fr_prime", "fq_representation_bound", "fr_representation_bound")) + tuple(
              "LimbRepresentation." + name for name in
              ("split_reconstruct", "split_canonical", "split_words_value", "split_words_canonical",
               "split_words_length", "montgomery_radix_agreement", "canonical_residue_preserved",
               "join_canonical", "join_split", "split_join", "join_split_words", "four_word_conversion",
               "canonical_digits_unique", "canonical_residue_digits_unique"))


def validate_fields(config):
    if set(config.get("fields", {})) != {"fq", "fr"}:
        raise ValueError("both exact field identities are required")


def certificate_rejected(text, filename, failure):
    return bool(str(failure).startswith("verification process failed (1);") and
                re.search(r'File "(?:\./)?' + re.escape(filename)
                         + r'", line \d+, characters \d+-\d+:\s*'
                         + r'Error: Unable to unify "true" with "false"\.', text))


def main():
    with formal.exclusive_lock():
        output = formal.WORK / "decaf-constants-proof"
        output.mkdir(exist_ok=True)
        report_path = output / "report.json"
        report = dict(status="blocked", completed=False, full_certification=False,
                      scope="shared Fq/Fr primality, bounds and limb-conversion arithmetic; not native execution or group refinement",
                      theorem_roots=ROOTS, commands=[], negative_controls=[])
        atomic_json(report_path, report)
        env = dict(os.environ, OPAMROOTISOK="1", OCAMLPATH="", COQPATH="")
        work = Path(tempfile.mkdtemp(prefix="replay-", dir=output))

        def command(argv, rejection=None):
            argv = list(map(str, argv))
            log = work / (str(len(report["commands"])) + ".log")
            report["commands"].append(dict(argv=argv, cwd=str(work), log=str(log)))
            atomic_json(report_path, report)
            try:
                bounded_run(argv, work, env, log, work / "unused", work, 600)
            except RuntimeError as failure:
                text = log.read_text()
                if rejection and certificate_rejected(text, rejection, failure):
                    return text
                raise
            if rejection:
                raise ValueError("composite modulus mutation was accepted")
            return log.read_text()

        try:
            config_path = formal.ROOT / "decaf/proofs/toolchain.json"
            config = json.loads(config_path.read_text())
            validate_fields(config)
            build_path = formal.WORK / "decaf-fiat-build/report.json"
            build_hash = formal.file_digest(build_path)
            build = json.loads(build_path.read_text())
            source = validate_proof_build(config_path, build, formal.ROOT / "decaf/proofs/fiat-array-index.patch")
            proof = formal.ROOT / "decaf/proofs/rocq/FieldConstants.v"
            representation = formal.ROOT / "decaf/proofs/rocq/LimbRepresentation.v"
            report.update(runner_sha256=formal.file_digest(Path(__file__)),
                          proof_sha256=formal.file_digest(proof),
                          representation_sha256=formal.file_digest(representation),
                          toolchain_sha256=formal.file_digest(config_path),
                          build_receipt_sha256=build_hash, build_receipt=build,
                          helper_hashes={name: formal.file_digest(formal.ROOT / name) for name in
                                         ("decaf_fiat_proof.py", "decaf_go_proof.py", "decaf_inventory.py", "formal.py", "security.py")})
            prefix = ["opam", "exec", "--switch=decaf-fv", "--", "rocq"]
            driver = Path(command(["opam", "exec", "--switch=decaf-fv", "--", "which", "rocq"]).strip()).resolve(strict=True)
            if str(driver) != build["compiler"]["path"] or formal.file_digest(driver) != build["compiler"]["sha256"]:
                raise ValueError("Rocq driver differs from the source build")
            if command([*prefix, "-v"]) != build["rocq_version"]:
                raise ValueError("Rocq runtime version differs from the source build")
            report["compiler"] = build["compiler"]
            flags = ["-Q", source / "coqprime/src/Coqprime", "Coqprime", "-Q", work, ""]
            shutil.copyfile(proof, work / "FieldConstants.v")
            command([*prefix, "compile", *flags, "FieldConstants.v"])
            shutil.copyfile(representation, work / "LimbRepresentation.v")
            command([*prefix, "compile", *flags, "LimbRepresentation.v"])
            audit = "From Stdlib Require Import ZArith.\nRequire Import FieldConstants LimbRepresentation.\n"
            for field, modulus in config["fields"].items():
                audit += f"Example {field}_identity : FieldConstants.{field}_modulus = ({modulus})%Z := eq_refl.\n"
            audit += f"Example rust_radix_identity : LimbRepresentation.radix32 = (2 ^ {config['representations']['rust']})%Z := eq_refl.\n"
            audit += f"Example go_radix_identity : LimbRepresentation.radix64 = (2 ^ {config['representations']['go']})%Z := eq_refl.\n"
            audit += "\n".join("Print Assumptions " + root + "." for root in ROOTS) + "\n"
            (work / "Audit.v").write_text(audit)
            validate_assumptions(command([*prefix, "compile", *flags, "Audit.v"]), ROOTS)
            command([*prefix, "check", "-bytecode-compiler", "no", "-silent", *flags,
                     "FieldConstants", "LimbRepresentation", "Audit"])
            for field, modulus in config["fields"].items():
                # Replace both the claimed constant and its certificate number.
                # Keeping the predecessor witness makes the checker reject n+2.
                mutant = proof.read_text().replace(str(modulus), str(int(modulus) + 2))
                if mutant == proof.read_text():
                    raise ValueError("modulus mutation did not match the proof")
                name = field + "Mutant.v"
                (work / name).write_text(mutant)
                command([*prefix, "compile", *flags, name], rejection=name)
                report["negative_controls"].append(dict(field=field, status="passed",
                    mutant_sha256=formal.file_digest(work / name)))
            if formal.file_digest(build_path) != build_hash:
                raise ValueError("source-build receipt changed during replay")
            validate_proof_build(config_path, build, formal.ROOT / "decaf/proofs/fiat-array-index.patch")
            if formal.file_digest(proof) != report["proof_sha256"]:
                raise ValueError("proof source changed during replay")
            if formal.file_digest(representation) != report["representation_sha256"]:
                raise ValueError("representation source changed during replay")
            if formal.file_digest(driver) != report["compiler"]["sha256"]:
                raise ValueError("Rocq driver changed during replay")
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report["detail"] = str(error) or "interrupted"
        finally:
            atomic_json(report_path, report)
        print(json.dumps(dict(status=report["status"], report=str(report_path))))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
