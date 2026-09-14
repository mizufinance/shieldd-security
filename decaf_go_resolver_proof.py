"""Replay constructed Go field dispatch and its conditional addition connection."""
import json
import hashlib
from pathlib import Path
import re
import shutil
import tempfile

import formal
import decaf_go_field_proof as field
import decaf_perennial_build as semantics
from decaf_inventory import MATRIX, validate
from decaf_toolchain import native_artifact
from decaf_fiat_build import build_environment
from decaf_inventory import atomic_json
from decaf_go_proof import validate_assumptions
import decaf_go_resolver as resolver
import decaf_go_specialization as specialization
from security import bounded_run

ROOTS = ("GoFieldResolver.constructed_contracts", "GoResolvedFieldAdd.resolved_fq_add",
         "GoResolvedFieldAdd.resolved_fr_add") + tuple("GoFieldEncoding." + name for name in (
             "encode_injective", "array_length", "decode_encode", "decode_sound", "wrong_array_length",
             "reject_empty_four", "replace_length", "replace_forall", "replace_here", "replace_elsewhere",
             "encoded_lookup", "bounded_lookup", "replace_wellformed", "call_roundtrip", "call_sound",
             "call_injective")) + tuple("GoFieldMemory." + name for name in (
                 "address_one", "word_array_append", "word_array_window", "word_array_element", "native_four_view")) + specialization.ROOTS
FOUNDATIONS = ("GoFieldEncoding", "GoFieldMemory", *specialization.HANDWRITTEN)
SPECIAL_CONTROLS = {"wrong-specialized-literal": "GoFullSpecialization",
                    "omitted-callee": "GoFieldCallRanks", "wrong-literal-dispatch": "GoLiteralDispatch"}
CASES = ("original", "wrong-underlying", "wrong-dispatch", "wrong-array-length", "wrong-address", *SPECIAL_CONTROLS)
PARENT_HELPERS = ("decaf_go_field_proof.py", "decaf_go_proof.py", "decaf_fiat_proof.py",
                  "decaf_fiat_build.py", "decaf_perennial_build.py", "decaf_toolchain.py",
                  "decaf_inventory.py", "formal.py", "security.py")


def parent_inputs():
    proofs = formal.ROOT / "decaf/proofs"
    paths = [proofs / "toolchain.json", formal.ROOT / "decaf/inputs.json", MATRIX,
             formal.WORK / "decaf-fields/report.json", formal.WORK / "decaf-perennial-build/report.json",
             proofs / "go-fields/field_test.go"]
    paths += [formal.ROOT / name for name in PARENT_HELPERS]
    paths += [proofs / "rocq" / (name + ".v") for name in field.MODULES]
    return {str(path.resolve(strict=True)): formal.file_digest(path) for path in paths}


def validate_parent(report):
    if (report.get("status") != "passed" or report.get("completed") is not True or
            report.get("full_certification") is not False or report.get("theorem_roots") != list(field.ROOTS) or
            report.get("witness_host") != "x86_64-unknown-linux-gnu" or
            set(report.get("cases", {})) != {name for name, _, _ in field.CASES} or
            report.get("input_hashes") != parent_inputs()):
        raise ValueError("missing, stale or incomplete parent Go field replay")
    config = json.loads((field.PROOFS / "toolchain.json").read_bytes())
    matrix = json.loads(MATRIX.read_bytes())
    validate(matrix)
    generation = formal.WORK / "decaf-fields"
    field.validate_generation(config, json.loads((generation / "report.json").read_bytes()), generation)
    build_path = formal.WORK / "decaf-perennial-build/report.json"
    build = json.loads(build_path.read_bytes())
    semantics.validate_build(build, config)
    if report.get("semantics_build_sha256") != formal.file_digest(build_path):
        raise ValueError("parent Go semantics build identity changed")
    expected_adoption = {"revision": matrix["sources"]["go"]["revision"], "files": {
        "internal/fiat/" + name + ".go": formal.file_digest(generation / "go" / (name + ".go"))
        for name in ("fq", "fr")}}
    if report.get("adopted_go_source") != expected_adoption:
        raise ValueError("parent Go source identity changed")
    goroot = Path(report["environment"]["GOROOT"]).resolve(strict=True)
    required_environment = {"GOOS": "linux", "GOARCH": "amd64", "GOAMD64": "v1", "CGO_ENABLED": "0",
                            "GOFLAGS": "", "GOEXPERIMENT": "", "GOENV": "off", "GOWORK": "off",
                            "GOTOOLCHAIN": "local", "GOPROXY": "off", "GOSUMDB": "off",
                            "GOMAXPROCS": "1", "GOGC": "100", "GODEBUG": "", "GOMEMLIMIT": "off"}
    if any(report["environment"].get(name) != value for name, value in required_environment.items()):
        raise ValueError("parent Go build/runtime settings changed")
    runtime = json.loads((formal.ROOT / "decaf/inputs.json").read_bytes())
    go_module = ("module mizufinance.local/decaf/fiat\n\ngo " + runtime["go"] + "\n").encode()
    field.validate_go_sources(goroot, report["go_sources"])
    tools = {(goroot / "bin/go").resolve(strict=True), (formal.CACHE / "goose").resolve(strict=True)}
    tools |= {(goroot / "pkg/tool/linux_amd64" / name).resolve(strict=True) for name in ("compile", "link", "asm")}
    tools |= {(goroot / name).resolve(strict=True) for name in report["go_sources"]}
    tools |= {Path(name) for name in build["tools"]}
    if report.get("tools") != {str(path): formal.file_digest(path) for path in tools}:
        raise ValueError("missing or changed parent tool inventory")
    if formal.file_digest(formal.CACHE / "goose") != native_artifact(config, "goose")["binary_sha256"]:
        raise ValueError("unrecognized parent Goose executable")
    root = Path(report["run_root"]).resolve(strict=True)
    if not root.is_relative_to((formal.WORK / "decaf-go-field-proof-replay").resolve(strict=True)):
        raise ValueError("parent case root escapes replay directory")

    def command_log(argv, cwd):
        matches = [entry for entry in report.get("commands", []) if entry.get("argv") == list(map(str, argv))
                   and entry.get("cwd") == str(cwd)]
        if len(matches) != 1 or str(Path(matches[0]["log"]).resolve(strict=True)) not in report["logs"]:
            raise ValueError("missing or ambiguous parent proof/control command log")
        return Path(matches[0]["log"]).read_text()

    prefix = ["opam", "exec", "--switch=decaf-fv", "--"]
    library = Path(build["library_root"])
    worker = (library / "rocq-runtime/rocqworker").resolve(strict=True)
    checker = (library.parent / "bin/rocqchk").resolve(strict=True)
    perennial = Path(build["source_root"])
    actual = set()
    for name, mutated_field, kind in field.CASES:
        case = root / name
        evidence = report["cases"][name]
        if Path(evidence["directory"]).resolve(strict=True) != case:
            raise ValueError("unexpected parent case directory")
        if (case / "go.mod").read_bytes() != go_module:
            raise ValueError("parent Go module or language version changed")
        native_status = ("passed" if mutated_field is None else "expected arithmetic rejection" if kind == "modulus"
                         else "expected offset/frame rejection")
        proof_status = ("compiled, closed global assumptions, recursively kernel rechecked" if mutated_field is None
                        else "expected arithmetic rejection" if kind == "modulus" else "expected execution-order rejection")
        if evidence.get("native_status") != native_status or evidence.get("proof_status") != proof_status:
            raise ValueError("parent case did not reach its required proof/control stage")
        extracted = case / "extraction/mizufinance_local/decaf/fiat.v"
        if evidence.get("extraction_sha256") != formal.file_digest(extracted):
            raise ValueError("parent extraction identity changed")
        flags = ["-Q", perennial / "src", "Perennial", "-Q", perennial / "new", "New",
                 "-Q", case / "extraction", "New.code", "-Q", case / "support", ""]
        rejected = None if mutated_field is None else {"fq": "GoFieldAdd", "fr": "GoFrFieldAdd"}[mutated_field]
        compiled = field.MODULES if rejected is None else field.MODULES[:field.MODULES.index(rejected)]
        sources = compiled if rejected is None else (*compiled, rejected)
        required_sources = [case / "extraction/math/bits.v", extracted]
        required_sources += [case / "support" / (module + ".v") for module in sources]
        for proof in required_sources:
            required_paths = [proof]
            if proof.stem != rejected:
                required_paths.append(proof.with_suffix(".vo"))
            if any(str(path.resolve(strict=True)) not in report["artifacts"] for path in required_paths):
                raise ValueError("parent control omits a required extraction/helper artifact")
            proof_log = command_log([*prefix, worker, "--kind=compile", *flags, proof], root)
            if proof.stem == rejected:
                field.validate_field_rejection(proof_log, proof.read_text(), mutated_field, proof.resolve(), kind)
        native_log = command_log([(goroot / "bin/go").resolve(strict=True), "test", "-p", "1", "-vet=off", "-count=1", "./..."], case)
        if mutated_field is not None:
            field.validate_native_rejection(native_log, mutated_field, kind)
        else:
            audit = case / "support/Audit.v"
            audit_text = ("Require Import " + " ".join(dict.fromkeys(item.split(".")[0] for item in field.ROOTS)) + ".\n" +
                          "\n".join("Print Assumptions " + item + "." for item in field.ROOTS) + "\n")
            if audit.read_text() != audit_text:
                raise ValueError("parent assumption audit source changed")
            validate_assumptions(command_log([*prefix, worker, "--kind=compile", *flags, audit], root), field.ROOTS)
            command_log([*prefix, checker, "-bytecode-compiler", "yes", "-silent", *flags, *field.MODULES, "Audit"], root)
        actual |= {str(path.resolve()) for path in case.rglob("*") if path.is_file() and
                   (path.suffix in {".go", ".v", ".vo", ".vos", ".vok"} or path.name in {"go.mod", "go.sum"})}
        for field_name in ("fq", "fr"):
            source = (generation / "go" / (field_name + ".go")).read_bytes()
            if mutated_field == field_name:
                mutator = field.modulus_mutation if kind == "modulus" else field.early_write_mutation
                source = mutator(source.decode(), field_name).encode()
            if (case / (field_name + ".go")).read_bytes() != source:
                raise ValueError("parent native source or source mutation changed")
        for source in (case / "support").glob("*.v"):
            if source.name != "Audit.v" and source.read_bytes() != (field.PROOFS / "rocq" / source.name).read_bytes():
                raise ValueError("parent proof copy changed")
        if (case / "field_test.go").read_bytes() != (field.PROOFS / "go-fields/field_test.go").read_bytes():
            raise ValueError("parent native witness copy changed")
        if mutated_field is not None:
            module = {"fq": "GoFieldAdd", "fr": "GoFrFieldAdd"}[mutated_field]
            if evidence.get("rejected_module") != module or (case / "support" / (module + ".vo")).exists():
                raise ValueError("parent negative control did not reject its intended module")
    expected = {name for name in report["artifacts"] if Path(name).suffix in {".go", ".v", ".vo", ".vos", ".vok"}
                or Path(name).name in {"go.mod", "go.sum"}}
    if actual != expected:
        raise ValueError("parent artifact inventory is incomplete")
    original = root / "original"
    required = {str((original / "support" / (name + suffix)).resolve(strict=True))
                for name in (*field.MODULES, "Audit") for suffix in (".v", ".vo")}
    required |= {str((original / "extraction" / name).resolve(strict=True)) for name in
                 ("math/bits.v", "math/bits.vo", "mizufinance_local/decaf/fiat.v", "mizufinance_local/decaf/fiat.vo")}
    if not required <= report["artifacts"].keys():
        raise ValueError("parent replay omits a reached proof import")
    if set(report["logs"]) != {str(Path(command["log"]).resolve(strict=True)) for command in report["commands"]}:
        raise ValueError("parent command log inventory is incomplete")
    for category in ("input_hashes", "tools", "artifacts", "logs"):
        for name, digest in report[category].items():
            if formal.file_digest(Path(name)) != digest:
                raise ValueError("changed parent replay artifact: " + name)
    return original, build


def mutate(source, kind):
    if kind == "wrong-specialized-literal":
        body = specialization.declaration(source, "FqAddⁱᵐᵖˡ")
        reads = [line for line in body.splitlines() if "IndexRef" in line and '"arg1"' in line]
        old = "(encode Uint64 (W64 0))"
        if not reads or old not in reads[0]:
            raise ValueError("specialized addition index control no longer matches")
        changed = reads[0].replace(old, "(encode Uint64 (W64 1))", 1)
        return source.replace(body, body.replace(reads[0], changed, 1), 1)
    old, new = {
        "wrong-underlying": ("if decide (t = fiat.FqUint1) then fiat.FqUint1ⁱᵐᵖˡ else",
                             "if decide (t = fiat.FqUint1) then fiat.FqInt1ⁱᵐᵖˡ else"),
        "wrong-dispatch": ("if decide (name = fiat.FqAdd) then as_function fiat.FqAddⁱᵐᵖˡ else",
                           "if decide (name = fiat.FqAdd) then as_function fiat.FqSubⁱᵐᵖˡ else"),
        "wrong-array-length": ("if Nat.eqb (List.length vs) n then traverse (decode element) vs else None",
                               "if true then traverse (decode element) vs else None"),
        "wrong-address": ("Definition word_address l i := loc_add l (Z.of_nat i).",
                          "Definition word_address l i := loc_add l (2 * Z.of_nat i)."),
        "omitted-callee": ("[literal_bits.Add64;", "["),
        "wrong-literal-dispatch": ("| IdFqAdd => @literal_fiat.FqAddⁱᵐᵖˡ field_syntax",
                                   "| IdFqAdd => @literal_fiat.FqSubⁱᵐᵖˡ field_syntax"),
    }[kind]
    if source.count(old) != 1 or (kind != "omitted-callee" and new in source):
        raise ValueError("resolver control no longer matches")
    return source.replace(old, new)


def validate_rejection(output, source, path, kind):
    name = {"wrong-underlying": "underlying_FqUint1", "wrong-dispatch": "resolve_FqAdd",
            "wrong-array-length": "reject_empty_four", "wrong-address": "address_one",
            "wrong-specialized-literal": "specializes_FqAdd", "omitted-callee": "ranked_FqMul",
            "wrong-literal-dispatch": "dispatch_FqAdd"}[kind]
    lines = source.splitlines()
    starts = [i for i, line in enumerate(lines) if line.startswith("Lemma " + name + " :")]
    sites = []
    if len(starts) == 1:
        for i in range(starts[0] + 1, len(lines)):
            if "reflexivity." in lines[i]:
                sites.append(i + 1)
            if "Qed." in lines[i]:
                break
    errors = re.findall(r'^File "([^"\n]+)", line (\d+), characters \d+-\d+:\s*\nError:', output, re.M)
    if (len(sites) != 1 or len(errors) != 1 or len(re.findall(r'^Error:', output, re.M)) != 1 or
            errors[0][0] != str(path.resolve(strict=True)) or int(errors[0][1]) != sites[0] or
            "Unable to unify" not in output.split("\nError:", 1)[1]):
        raise ValueError("resolver control failed outside the intended contract proof")


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-go-resolver-proof"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "constructive field values, specialized syntax/dispatch, literal array ownership and conditional Fq/Fr addition",
                  "theorem_roots": list(ROOTS), "commands": [], "cases": {},
                  "inputs": {}, "artifacts": {}, "logs": {},
                  "kernel_reduction": "recursive checking with bytecode reduction; Rocq VM/compiler correctness is trusted",
                  "open_obligations": ["GoGlobalContext and GoLocalContext construction",
                      "compatible PreSemantics for the modified dispatch instance", "native execution correspondence",
                      "termination", "multiplication, group, encoding, compiled trace and consumer closure"]}
        atomic_json(report_path, report)
        env = build_environment()
        env["OCAMLRUNPARAM"] = "s=2M,o=20,O=50"
        run = work

        def bind(path, category="artifacts"):
            path = Path(path).resolve(strict=True)
            digest = formal.file_digest(path)
            if str(path) in report[category] and report[category][str(path)] != digest:
                raise ValueError("changed resolver artifact before reuse")
            report[category][str(path)] = digest

        def command(argv, reject=False, timeout=900):
            log = run / f"{len(report['commands']):03}.log"
            argv = list(map(str, argv))
            report["commands"].append({"argv": argv, "log": str(log)})
            atomic_json(report_path, report)
            failed = False
            try:
                bounded_run(argv, run, env, log, run / "unused", run, timeout)
            except RuntimeError as error:
                if not reject or "verification process failed (1)" not in str(error):
                    raise
                failed = True
            finally:
                if log.is_file():
                    bind(log, "logs")
            if failed != reject:
                raise ValueError("unexpected resolver command status")
            return log.read_text()

        try:
            run = Path(tempfile.mkdtemp(prefix="run-", dir=work)).resolve()
            report["run_root"] = str(run)
            parent_path = formal.WORK / "decaf-go-field-proof-replay/report.json"
            data = parent_path.read_bytes()
            report["inputs"][str(parent_path.resolve())] = hashlib.sha256(data).hexdigest()
            parent = json.loads(data)
            original, build = validate_parent(parent)
            handwritten = field.PROOFS / "rocq/GoResolvedFieldAdd.v"
            foundation_paths = {name: field.PROOFS / "rocq" / (name + ".v") for name in FOUNDATIONS}
            for path in (formal.ROOT / "decaf_go_resolver.py", formal.ROOT / "decaf_go_resolver_proof.py",
                         formal.ROOT / "decaf_go_specialization.py", handwritten, *foundation_paths.values()):
                bind(path, "inputs")
            def parent_source(path):
                data = path.read_bytes()
                if hashlib.sha256(data).hexdigest() != parent["artifacts"].get(str(path.resolve(strict=True))):
                    raise ValueError("resolver read source bytes outside the parent binding")
                return data

            field_bytes = parent_source(original / "extraction/mizufinance_local/decaf/fiat.v")
            bits_bytes = parent_source(original / "extraction/math/bits.v")
            generated = resolver.render(field_bytes, bits_bytes)
            specialized = specialization.render(field_bytes, bits_bytes)
            perennial = Path(build["source_root"])
            library = Path(build["library_root"])
            worker = (library / "rocq-runtime/rocqworker").resolve(strict=True)
            checker = (library.parent / "bin/rocqchk").resolve(strict=True)
            prefix = ["opam", "exec", "--switch=decaf-fv", "--"]

            def current():
                validate_parent(parent)
                for category in ("inputs", "artifacts", "logs"):
                    for name, digest in report[category].items():
                        if formal.file_digest(Path(name)) != digest:
                            raise ValueError("changed resolver replay input or artifact: " + name)
                actual = {str(path.resolve()) for case in report["cases"].values()
                          for path in Path(case["directory"]).rglob("*") if path.is_file() and
                          path.suffix in {".v", ".vo", ".vos", ".vok"}}
                if actual != set(report["artifacts"]):
                    raise ValueError("resolver source/proof artifact inventory changed")

            for name in CASES:
                case = run / name
                case.mkdir()
                evidence = report["cases"][name] = {"directory": str(case), "status": "pending"}
                flags = ["-Q", perennial / "src", "Perennial", "-Q", perennial / "new", "New",
                         "-Q", original / "extraction", "New.code", "-Q", original / "support", "", "-Q", case, ""]
                if name in SPECIAL_CONTROLS:
                    flags = flags[:-3] + ["-Q", run / "original", "", *flags[-3:]]

                def compile_proof(path, reject=False):
                    bind(path)
                    output = command([*prefix, worker, "--kind=compile", *flags, path], reject=reject)
                    if path.with_suffix(".vo").exists() == reject:
                        raise ValueError("unexpected compiled artifact at resolver proof stage")
                    for suffix in (".vo", ".vos", ".vok"):
                        if path.with_suffix(suffix).is_file():
                            bind(path.with_suffix(suffix))
                    return output

                if name in SPECIAL_CONTROLS:
                    current()
                    module = SPECIAL_CONTROLS[name]
                    source = mutate(specialized[module], name)
                    proof = case / (module + ".v")
                    proof.write_text(source)
                    output = compile_proof(proof, reject=True)
                    validate_rejection(output, source, proof, name)
                    evidence["status"] = "expected specialization proof rejection"
                    current()
                    atomic_json(report_path, report)
                    continue
                if name in ("original", "wrong-array-length", "wrong-address"):
                    for module, original_proof in foundation_paths.items():
                        data = original_proof.read_bytes()
                        if hashlib.sha256(data).hexdigest() != report["inputs"][str(original_proof.resolve())]:
                            raise ValueError("constructive foundation proof changed before copying")
                        text = data.decode("utf-8")
                        reject = (name, module) in (("wrong-array-length", "GoFieldEncoding"),
                                                  ("wrong-address", "GoFieldMemory"))
                        source = mutate(text, name) if reject else text
                        proof = case / (module + ".v")
                        proof.write_text(source)
                        output = compile_proof(proof, reject=reject)
                        if reject:
                            validate_rejection(output, source, proof, name)
                            evidence["status"] = "expected constructive foundation proof rejection"
                            break
                    if name != "original":
                        current()
                        atomic_json(report_path, report)
                        continue
                    for module, text in specialized.items():
                        proof = case / (module + ".v")
                        proof.write_text(text)
                        compile_proof(proof)
                source = generated if name == "original" else mutate(generated, name)
                proof = case / "GoFieldResolver.v"
                proof.write_text(source)
                output = compile_proof(proof, reject=name != "original")
                if name != "original":
                    validate_rejection(output, source, proof, name)
                    evidence["status"] = "expected contract proof rejection"
                else:
                    target = case / handwritten.name
                    shutil.copyfile(handwritten, target)
                    if formal.file_digest(target) != report["inputs"][str(handwritten.resolve())]:
                        raise ValueError("resolver connection proof copy changed")
                    compile_proof(target)
                    audit = case / "ResolverAudit.v"
                    audit.write_text("Require Import GoFieldResolver GoResolvedFieldAdd " +
                                     " ".join((*FOUNDATIONS, *specialization.GENERATED)) + ".\n" +
                                     "\n".join("Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    validate_assumptions(compile_proof(audit), ROOTS)
                    current()
                    command([*prefix, checker, "-bytecode-compiler", "yes", "-silent", *flags,
                             "GoFieldResolver", "GoResolvedFieldAdd", *FOUNDATIONS, *specialization.GENERATED,
                             "ResolverAudit"], timeout=2400)
                    current()
                    evidence["status"] = "compiled, closed global assumptions, recursively kernel rechecked"
                current()
                atomic_json(report_path, report)
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report.update(status="failed", completed=False, detail=str(error) or "interrupted")
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
