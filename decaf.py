#!/usr/bin/env python3
"""Run revision-bound Decaf functional tests and a bounded Linux binary pilot."""
import argparse
import io
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tarfile
import zipfile

import formal
from security import bounded_run

INPUTS = formal.ROOT / "decaf/inputs.json"
LIMIT = 1800
SCALAR_ORDER = sum(n << (64 * i) for i, n in enumerate([
    13356249993388743167, 5950279507993463550,
    10965441865914903552, 336320092672043349,
]))


class Blocked(RuntimeError):
    pass


def digest_tree(root):
    return {str(p.relative_to(root)): formal.file_digest(p)
            for p in sorted(root.rglob("*")) if p.is_file() and "__pycache__" not in p.parts}


def validate_inputs(inputs):
    if inputs["target"] != "x86_64-unknown-linux-gnu":
        raise ValueError("unsupported leakage target")
    for name in ("rust", "go"):
        item = inputs["libraries"][name]
        if set(item) != {"repository", "original", "candidate"}:
            raise ValueError("incomplete library dependency identity")
        for key in ("original", "candidate"):
            if not re.fullmatch("[0-9a-f]{40}", item[key]):
                raise ValueError("library revision must be a full commit SHA")


def classify_analysis(log, expected, endpoint):
    """A tool error is never a successful negative control."""
    states = re.findall(r"Program status is\s*:\s*(secure|insecure|unknown)\b", log)
    if len(states) != 1:
        return "blocked", "missing or ambiguous BINSEC verdict"
    state = states[0]
    if state == "unknown":
        return "blocked", "BINSEC exploration or solver checks incomplete"
    if state == "insecure":
        if not re.search(r"(control flow|memory access) leak", log, re.I):
            return "blocked", "insecure verdict lacks a leakage diagnostic"
        return ("passed" if expected == "insecure" else "failed"), "leakage counterexample"
    if expected == "insecure":
        return "failed", "negative control did not expose the intended leak"
    if re.search(r"Exploration is incomplete|unsupported|unknown instruction", log, re.I):
        return "blocked", "incomplete analysis cannot establish the boundary"
    # A vacuous secure verdict (e.g. impossible input assumptions) is insufficient.
    reached = re.findall(r"^\[sse:result\] Path \d+ reached address (0x[0-9a-f]+)\b", log, re.M | re.I)
    if endpoint not in [int(address, 16) for address in reached]:
        return "blocked", "no evidence that the output boundary was reached"
    return "passed", "complete relational analysis for the declared snapshot/input domain"


def validate_analysis_config(text):
    # No reached dependency may be replaced by an assumed-safe summary or cut.
    if re.search(r"\b(replace|hook|cut)\b", text, re.I):
        raise ValueError("analysis may not omit or summarize transitive dependencies")
    if len(re.findall(r"^halt at 0x[0-9a-f]+$", text, re.M)) != 1:
        raise ValueError("analysis requires exactly one output boundary")


def routing_mutation(source):
    path = source / "src/ark_curve/ops/projective.rs"
    text = path.read_text()
    old = """impl<'a> MulAssign<&'a mut Fr> for Element {
    fn mul_assign(&mut self, point: &'a mut Fr) {
        *self *= &*point;
    }
}"""
    new = """impl<'a> MulAssign<&'a mut Fr> for Element {
    fn mul_assign(&mut self, point: &'a mut Fr) {
        let mut p = self.inner;
        p *= *point;
        *self = Element { inner: p };
    }
}"""
    if text.count(old) != 1:
        raise Blocked("routing mutation no longer matches the pinned implementation")
    path.write_text(text.replace(old, new))


class Pilot:
    def __init__(self, mode, language):
        self.mode, self.language = mode, language
        self.inputs = json.loads(INPUTS.read_text())
        validate_inputs(self.inputs)
        self.work = formal.WORK / "decaf"
        self.reports = self.work / f"{mode}-report"
        self.reports.mkdir(parents=True, exist_ok=True)
        self.env = dict(os.environ, CARGO_BUILD_JOBS="2", RAYON_NUM_THREADS="2",
                        GOMAXPROCS="2", GOFLAGS="-p=2", CARGO_INCREMENTAL="0",
                        GIT_LFS_SKIP_SMUDGE="1", CARGO_TARGET_DIR=str(formal.CACHE / "decaf-rust-target"))
        self.report = {"status": "running", "full_certification": False,
                       "security_revision": formal.run(["git", "rev-parse", "HEAD"], cwd=formal.ROOT, capture=True).strip(),
                       "inputs": self.inputs, "harness_hashes": digest_tree(formal.ROOT / "decaf"),
                       "runner_sha256": formal.file_digest(Path(__file__)),
                       "helper_hashes": {name: formal.file_digest(formal.ROOT / name) for name in ("formal.py", "security.py")},
                       "host": platform.platform(), "checks": []}

    def command(self, args, cwd, case, timeout=LIMIT, env=None, snapshots=None):
        case.setdefault("commands", []).append({"argv": list(map(str, args)), "cwd": str(cwd)})
        log = self.reports / f"{case['id']}-{len(case['commands'])}.log"
        bounded_run(list(map(str, args)), cwd, env or self.env, log,
                    snapshots or self.work / "unused", self.reports, timeout)
        return log.read_text(errors="replace")

    def tool(self, command, version):
        if not shutil.which(command):
            raise Blocked(f"required tool unavailable: {command} {version}")
        flag = "version" if command == "go" else "-version" if command == "binsec" else "--version"
        text = subprocess.check_output([command, flag], text=True).strip()
        if not re.search(r"(?<![\d.])" + re.escape(version) + r"(?![\d.])", text):
            raise Blocked(f"expected {command} {version}; found {text}")
        self.report.setdefault("tools", {})[command] = text

    def checkout(self, language, revision, case):
        item = self.inputs["libraries"][language]
        sha = item[revision]
        mirror = formal.CACHE / f"decaf-{language}.git"
        if not mirror.exists():
            self.command(["git", "init", "--bare", mirror], formal.ROOT, case)
        self.command(["git", "--git-dir", mirror, "fetch", "--depth=1", item["repository"], sha], formal.ROOT, case)
        checkout = self.work / f"source-{language}"
        if checkout.exists():
            shutil.rmtree(checkout)
        checkout.mkdir(parents=True)
        archive = subprocess.check_output(["git", "--git-dir", str(mirror), "archive", "--format=zip", sha])
        with zipfile.ZipFile(io.BytesIO(archive)) as files:
            for member in files.namelist():
                if Path(member).is_absolute() or ".." in Path(member).parts:
                    raise ValueError("unsafe source archive path")
            files.extractall(checkout)
        case.update(library=language, revision=sha, source_tree=formal.run(
            ["git", "--git-dir", str(mirror), "rev-parse", sha + "^{tree}"], cwd=formal.ROOT, capture=True).strip())
        if language == "rust":
            shutil.copyfile(formal.ROOT / "decaf/Cargo.lock", checkout / "Cargo.lock")
        case["lock_sha256"] = formal.file_digest(checkout / ("Cargo.lock" if language == "rust" else "go.sum"))
        return checkout

    def check(self, name, kind, operation):
        print(f"{name}: running ({kind})", flush=True)
        case = {"id": name, "evidence_kind": kind, "status": "running"}
        self.report["checks"].append(case)
        try:
            operation(case)
            case.setdefault("detail", "completed")
            if case["status"] == "running":
                case["status"] = "passed"
        except Blocked as error:
            case.update(status="blocked", detail=str(error))
        except Exception as error:
            case.update(status="failed", detail=str(error))
        finally:
            self.save()
            print(f"{name}: {case['status']}: {case['detail']}", flush=True)

    def save(self):
        states = [c["status"] for c in self.report["checks"]]
        self.report["status"] = ("failed" if "failed" in states else "blocked" if "blocked" in states else "passed")
        (self.reports / "report.json").write_text(json.dumps(self.report, indent=2, sort_keys=True) + "\n")

    def functional(self, language, case):
        self.tool("rustc" if language == "rust" else "go", self.inputs["rustc" if language == "rust" else "go"])
        source = self.checkout(language, "candidate", case)
        if language == "rust":
            for features in ([], ["--no-default-features"], ["--features", "r1cs,u32_backend"]):
                threads = "1" if features == ["--features", "r1cs,u32_backend"] else "2"
                self.command(["cargo", "test", "--locked", "--release", *features, "--lib", "--tests", "--", f"--test-threads={threads}"], source, case)
        else:
            for flags in ([], ["-tags", "purego"]):
                self.command(["go", "test", "-mod=readonly", "-p", "2", *flags, "./..."], source, case)
            self.command(["go", "vet", "-mod=readonly", "-p", "2", "./..."], source, case)

    def build(self, language, revision, case, mutate=False):
        self.tool("rustc" if language == "rust" else "go", self.inputs["rustc" if language == "rust" else "go"])
        source = self.checkout(language, revision, case)
        if language == "rust":
            if mutate:
                routing_mutation(source)
                case["mutation_sha256"] = formal.file_digest(source / "src/ark_curve/ops/projective.rs")
            (source / "examples").mkdir(exist_ok=True)
            shutil.copyfile(formal.ROOT / "decaf/rust.rs", source / "examples/ct_pilot.rs")
            env = dict(self.env, RUSTFLAGS="-C debuginfo=2 -C relocation-model=static -C link-arg=-no-pie")
            case["build_environment"] = {"RUSTFLAGS": env["RUSTFLAGS"]}
            self.command(["cargo", "build", "--locked", "--release", "--example", "ct_pilot"], source, case, env=env)
            binary = Path(self.env["CARGO_TARGET_DIR"]) / "release/examples/ct_pilot"
        else:
            directory = source / "cmd/ct-pilot"
            directory.mkdir(parents=True)
            shutil.copyfile(formal.ROOT / "decaf/go.go", directory / "main.go")
            binary = source / "ct-pilot"
            self.command(["go", "build", "-mod=readonly", "-p", "2", "-o", binary, "./cmd/ct-pilot"], source, case)
        self.command([binary], source, case, timeout=60)
        case["binary_sha256"] = formal.file_digest(binary)
        return binary

    def analyze(self, binary, case, expected="secure", language="rust", mutable=False):
        if language == "go":
            entry, done, secret = "main.decafEntry", "main.decafDone", "main.secret"
        else:
            entry, done, secret = ("decaf_mut_entry" if mutable else "decaf_entry"), "decaf_done", "decaf_secret"
        symbols = self.command(["nm", "-S", "--defined-only", binary], binary.parent, case)
        addresses = {}
        for name in (entry, done, secret):
            match = re.search(r"^([0-9a-f]+)\s+([0-9a-f]+)\s+\w\s+" + re.escape(name) + "$", symbols, re.M)
            if not match:
                raise Blocked(f"missing live analysis symbol: {name}")
            addresses[name] = int(match[1], 16)
            if name == secret and int(match[2], 16) != 32:
                raise Blocked("secret storage is not exactly 32 bytes")
        snapshot_dir = self.work / "snapshot"
        if snapshot_dir.exists():
            shutil.rmtree(snapshot_dir)
        snapshot_dir.mkdir()
        core = snapshot_dir / "core"
        gdb = self.reports / f"{case['id']}.gdb"
        gdb.write_text(f"set pagination off\nset confirm off\nset env LD_BIND_NOW=1\nset disable-randomization on\nbreak *0x{addresses[entry]:x}\nrun\ngenerate-core-file {core}\nkill\nquit\n")
        try:
            case["snapshot_method"] = "native GDB"
            self.command(["gdb", "--batch", "-x", gdb, binary], binary.parent, case, timeout=120, snapshots=snapshot_dir)
        except (OSError, RuntimeError) as error:
            raise Blocked(f"initialized snapshot unavailable: {error}") from error
        case["snapshot_sha256"] = formal.file_digest(core)
        address = addresses[secret]
        cfg = self.reports / f"{case['id']}.cfg"
        text = f"starting from core with\n  @[0x{address:x}, 32] := secret\nend\n"
        if language == "rust":
            text += f"assume @[0x{address:x}, 32] < 0x{SCALAR_ORDER:064x}\n"
        text += f"reach 0x{addresses[done]:x}\nhalt at 0x{addresses[done]:x}\nexplore all\n"
        validate_analysis_config(text)
        cfg.write_text(text)
        case.update(symbols=addresses, analysis_config_sha256=formal.file_digest(cfg),
                    expected=expected, scope="one initialized public process snapshot; 256-bit inputs" if language != "rust" else "one initialized public process snapshot; canonical Montgomery Fr; public generator")
        replay = self.reports / f"{case['id']}-reproducer.tar.gz"
        with tarfile.open(replay, "w:gz") as archive:
            archive.add(binary, arcname="binary")
            archive.add(core, arcname="core")
            archive.add(cfg, arcname="analysis.cfg")
            archive.add(gdb, arcname="snapshot.gdb")
        case["reproducer_sha256"] = formal.file_digest(replay)
        try:
            log = self.command(["binsec", "-sse", "-checkct", "-checkct-leak-info", "halt",
                                "-checkct-stats-file", self.reports / f"{case['id']}.toml", "-sse-script", cfg,
                                "-sse-depth", "10000000", "-sse-timeout", str(LIMIT - 10), core], binary.parent, case)
        except RuntimeError as error:
            raise Blocked(f"binary-analysis execution did not complete: {error}") from error
        case["status"], case["detail"] = classify_analysis(log, expected, addresses[done])
        shutil.rmtree(snapshot_dir)

    def leakage(self):
        def prerequisites(case):
            if platform.system() != "Linux" or platform.machine() not in ("x86_64", "AMD64"):
                raise Blocked("leakage pilot requires Linux x86-64; native host is " + platform.platform())
            self.tool("binsec", self.inputs["binsec"]["version"])
            for tool in ("gdb", "nm", "cc"):
                if not shutil.which(tool):
                    raise Blocked("required analysis tool unavailable: " + tool)
            case["binsec_sha256"] = formal.file_digest(Path(shutil.which("binsec")))
        self.check("analysis-prerequisites", "tooling", prerequisites)
        ready = self.report["checks"][-1]["status"] == "passed"
        def guarded(operation):
            def call(case):
                if not ready:
                    raise Blocked("Linux x86-64 analysis prerequisites unavailable; see prerequisite check")
                operation(case)
            return call
        for control, number in (("safe", 0), ("branch", 1), ("address", 2)):
            def run_control(case, number=number):
                binary = self.work / f"control-{number}"
                self.command(["cc", "-g", "-O0", "-fno-pie", "-no-pie", f"-DCONTROL={number}", formal.ROOT / "decaf/controls.c", "-o", binary], formal.ROOT, case)
                case["binary_sha256"] = formal.file_digest(binary)
                self.analyze(binary, case, "secure" if number == 0 else "insecure", language="control")
            self.check("control-" + control, "negative_control" if number else "positive_control", guarded(run_control))
        ready = ready and all(c["status"] == "passed" for c in self.report["checks"])
        for language in ("rust", "go"):
            if self.language not in (language, "all"):
                continue
            for revision in ("original", "candidate"):
                def run_library(case, language=language, revision=revision):
                    binary = self.build(language, revision, case)
                    self.analyze(binary, case, "insecure" if revision == "original" else "secure", language)
                self.check(f"{language}-{revision}", "negative_control" if revision == "original" else "relational_analysis", guarded(run_library))
            if language == "rust":
                for mutation in (False, True):
                    def run_mutable(case, mutation=mutation):
                        binary = self.build("rust", "candidate", case, mutate=mutation)
                        self.analyze(binary, case, "insecure" if mutation else "secure", "rust", mutable=True)
                    self.check("rust-routing-mutation" if mutation else "rust-mutable", "negative_control" if mutation else "relational_analysis", guarded(run_mutable))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("functional", "leakage"))
    parser.add_argument("--language", choices=("rust", "go", "all"), default="all")
    args = parser.parse_args()
    with formal.exclusive_lock():
        reports = formal.WORK / "decaf" / f"{args.mode}-report"
        if reports.exists():
            shutil.rmtree(reports)
        try:
            pilot = Pilot(args.mode, args.language)
        except Exception as error:
            reports.mkdir(parents=True, exist_ok=True)
            (reports / "report.json").write_text(json.dumps({
                "status": "failed", "full_certification": False,
                "checks": [{"id": "bootstrap", "evidence_kind": "tooling", "status": "failed", "detail": str(error)}],
            }, indent=2) + "\n")
            return 1
        if args.mode == "leakage":
            pilot.leakage()
        else:
            for language in ("rust", "go"):
                if args.language in (language, "all"):
                    pilot.check(language + "-functional", "functional_test", lambda case, language=language: pilot.functional(language, case))
        print(json.dumps({"status": pilot.report["status"], "report": str(pilot.reports / "report.json")}))
        return 0 if pilot.report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
