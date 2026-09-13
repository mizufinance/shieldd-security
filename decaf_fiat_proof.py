#!/usr/bin/env python3
"""Check the typed Fiat multiplication pipeline; native correspondence remains open."""
import json
import os
from pathlib import Path
import shutil

import formal
from decaf_go_proof import validate_assumptions
from decaf_inventory import atomic_json
from decaf_toolchain import native_artifact
from security import bounded_run

ROOTS = tuple(f"FiatMultiply.{module}.{theorem}" for module in ("RustFq", "GoFq", "RustFr", "GoFr")
              for theorem in ("pipeline_success", "correct"))


def generation_options(language):
    common = ["--lang", "Rust" if language == "rust" else "Go", "--no-prefix-fiat", "--no-field-element-typedefs"]
    if language == "rust":
        return common + ["--public-type-case", "PascalCase", "--private-type-case", "PascalCase"]
    if language != "go":
        raise ValueError("unsupported native language")
    return common + ["--no-wide-int", "--relax-primitive-carry-to-bitwidth", "32,64", "--cmovznz-by-mul",
                     "--package-name", "fiat", "--public-function-case", "UpperCamelCase",
                     "--private-function-case", "camelCase", "--public-type-case", "UpperCamelCase",
                     "--private-type-case", "camelCase"]


def validate_generation(config, receipt, directory):
    build = native_artifact(config, "fiat")
    if (receipt.get("status") != "generated" or receipt.get("completed") is not True or
            receipt.get("fiat_revision") != config["fiat"]["revision"] or
            receipt.get("native_host") != build["host"] or
            receipt.get("generator_sha256") != build["binary_sha256"] or
            receipt.get("generator_patch_sha256") != build["printer_patch_sha256"]):
        raise ValueError("generation identity does not match the pinned native toolchain")
    if config["representations"] != {"rust": 32, "go": 64} or set(config["fields"]) != {"fq", "fr"}:
        raise ValueError("unsupported field or representation")
    expected_paths = {f"{language}/{field}.{extension}" for language, extension in (("rust", "rs"), ("go", "go"))
                      for field in ("fq", "fr")}
    entries = receipt.get("outputs", [])
    if len(entries) != 4 or {entry.get("path") for entry in entries} != expected_paths:
        raise ValueError("missing or duplicate generated arithmetic")
    for entry in entries:
        language, filename = entry["path"].split("/")
        field = filename.split(".")[0]
        expected = [".cache/fiat-crypto/src/ExtractionOCaml/fiat_crypto", "word-by-word-montgomery",
                    *generation_options(language), "--output", ".work/decaf-fields/" + entry["path"],
                    field, str(config["representations"][language]), config["fields"][field]]
        if [arg.replace("\\", "/") for arg in entry.get("command", [])] != expected:
            raise ValueError("generation options differ from the checked pipeline recipe")
        if formal.file_digest(directory / entry["path"]) != entry.get("sha256"):
            raise ValueError("generated arithmetic bytes differ from the receipt")


def validate_proof_build(config_path, receipt, patch):
    config = json.loads(config_path.read_text())
    expected_patch = native_artifact(config, "fiat")["printer_patch_sha256"]
    if formal.file_digest(patch) != expected_patch:
        raise ValueError("printer patch bytes differ from the reviewed patch")
    if (receipt.get("status") != "passed" or receipt.get("completed") is not True or
            receipt.get("patch_sha256") != expected_patch or
            receipt.get("toolchain_sha256") != formal.file_digest(config_path) or
            receipt.get("runner_sha256") != formal.file_digest(formal.ROOT / "decaf_fiat_build.py")):
        raise ValueError("missing or stale source build provenance")
    source = Path(receipt["source_root"]).resolve(strict=True)
    if not receipt.get("sources") or receipt["sources"][0]["revision"] != config["fiat"]["revision"]:
        raise ValueError("source build uses an unexpected Fiat revision")
    for category in ("source_files", "artifacts"):
        if not receipt.get(category):
            raise ValueError("empty proof build inventory")
        for relative, digest in receipt[category].items():
            path = (source / relative).resolve(strict=True)
            if not path.is_relative_to(source) or formal.file_digest(path) != digest:
                raise ValueError("proof build input or artifact changed")
    required = {"src/PushButtonSynthesis/WordByWordMontgomery.vo", "src/Stringification/Language.vo"}
    if not required <= receipt["artifacts"].keys():
        raise ValueError("source build omits required pipeline imports")
    actual = {str(path.relative_to(source)) for path in source.rglob("*")
              if path.is_file() and path.suffix in {".vo", ".cmxs", ".cma", ".so"}}
    if actual != receipt["artifacts"].keys():
        raise ValueError("unrecorded imported proof or plugin artifact")
    for name, target in receipt.get("source_links", {}).items():
        path = source / name
        if (not path.is_symlink() or os.readlink(path) != target or
                not path.resolve().is_relative_to(source)):
            raise ValueError("source link changed or escapes build")
    return source


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-fiat-proof"
        work.mkdir(exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "blocked", "completed": False, "full_certification": False,
                  "scope": "typed Fiat multiplication under Rust32/Go64 pipeline options; no native refinement",
                  "kernel_reduction": "Rocq checker with bytecode reduction enabled; Rocq VM/compiler correctness is trusted, as for vm_compute in these proof terms",
                  "open_obligations": ["native execution correspondence", "printer and emitted-helper correspondence",
                      "concrete language semantics", "native safety and termination", "compiled trace closure"],
                  "theorem_roots": ROOTS, "commands": []}
        atomic_json(report_path, report)
        env = dict(os.environ, OPAMROOTISOK="1", GIT_NO_REPLACE_OBJECTS="1", OCAMLPATH="", COQPATH="")
        def command(argv, timeout=300, cwd=work):
            argv = list(map(str, argv))
            log = work / f"{len(report['commands']):02}.log"
            report["commands"].append(argv)
            atomic_json(report_path, report)
            bounded_run(argv, cwd, env, log, work / "unused", work, timeout)
            return log.read_text()
        try:
            config_path = formal.ROOT / "decaf/proofs/toolchain.json"
            config = json.loads(config_path.read_text())
            generated = formal.WORK / "decaf-fields"
            receipt_path = generated / "report.json"
            receipt = json.loads(receipt_path.read_text())
            validate_generation(config, receipt, generated)
            patch = formal.ROOT / "decaf/proofs/fiat-array-index.patch"
            build_path = formal.WORK / "decaf-fiat-build/report.json"
            build = json.loads(build_path.read_text())
            fiat = validate_proof_build(config_path, build, patch)
            rocq = ["opam", "exec", "--switch=decaf-fv", "--", "rocq"]
            driver = Path(command(["opam", "exec", "--switch=decaf-fv", "--", "which", "rocq"]).strip()).resolve(strict=True)
            if str(driver) != build["compiler"]["path"] or formal.file_digest(driver) != build["compiler"]["sha256"]:
                raise ValueError("Rocq driver differs from the source build")
            if command([*rocq, "-v"]) != build["rocq_version"]:
                raise ValueError("Rocq runtime version differs from the source build")
            if command(["opam", "list", "--switch=decaf-fv", "--installed", "--columns=version", "--short", "rocq-runtime"]).strip() != config["rocq-runtime"]:
                raise ValueError("unexpected Rocq version")
            report.update(runner_sha256=formal.file_digest(Path(__file__)), toolchain_sha256=formal.file_digest(config_path),
                          proof_build_receipt_sha256=formal.file_digest(build_path), proof_build=build,
                          generation_receipt_sha256=formal.file_digest(receipt_path), generation=receipt,
                          proof_sha256=formal.file_digest(formal.ROOT / "decaf/proofs/rocq/FiatMultiply.v"),
                          helper_hashes={name: formal.file_digest(formal.ROOT / name) for name in
                                         ("formal.py", "security.py", "decaf_go_proof.py", "decaf_inventory.py", "decaf_toolchain.py")})
            flags = ["-R", fiat / "src", "Crypto", "-Q", fiat / "coqprime/src/Coqprime", "Coqprime",
                     "-Q", fiat / "rupicola/bedrock2/deps/coqutil/src/coqutil", "coqutil",
                     "-Q", fiat / "rewriter/src/Rewriter", "Rewriter", "-I", fiat / "rewriter/src/Rewriter/Util/plugins",
                     "-Q", work, ""]
            for name in ("FiatMultiply", "Audit"):
                for extension in ("vo", "vos", "vok", "glob"):
                    (work / f"{name}.{extension}").unlink(missing_ok=True)
            shutil.copyfile(formal.ROOT / "decaf/proofs/rocq/FiatMultiply.v", work / "FiatMultiply.v")
            command([*rocq, "compile", *flags, work / "FiatMultiply.v"], timeout=600)
            audit = "From Stdlib Require Import ZArith.\nRequire Import FiatMultiply.\n"
            for field, modulus in config["fields"].items():
                audit += f"Example {field}_identity : FiatMultiply.{field} = ({modulus})%Z := eq_refl.\n"
            audit += "\n".join("Print Assumptions " + name + "." for name in ROOTS) + "\n"
            (work / "Audit.v").write_text(audit)
            validate_assumptions(command([*rocq, "compile", *flags, work / "Audit.v"]), ROOTS)
            # The kernel checker does not accept compile-time ML include paths.
            kernel_flags = flags[:]
            index = kernel_flags.index("-I")
            del kernel_flags[index:index + 2]
            command([*rocq, "check", "-bytecode-compiler", "yes", "-m", *kernel_flags, "FiatMultiply", "Audit"], timeout=1200)
            validate_proof_build(config_path, build, patch)
            if formal.file_digest(driver) != build["compiler"]["sha256"]:
                raise ValueError("Rocq driver changed during replay")
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report["detail"] = str(error) or "interrupted"
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
