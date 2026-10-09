#!/usr/bin/env python3
"""Check the finite snapshot model and replay its traces through pinned Rust."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from security import run, source_identity
WORK = ROOT / ".work/state"
QUINT = ROOT / ".work/quint/node_modules/@informalsystems/quint/dist/src/cli.js"
QUINT_CLI_SHA = "ac12595b1cb7253feec93c79417615c6eb20fc3b6a3df35c5e3530b24e90a501"
QUINT_HOME = ROOT / ".work/quint-home"
JAR_SHA = "4753c0ebb2cbb266e2c6ac19ab5ca3827d726cc80fd1fc5d7c1eeb64736cd60b"
SCENARIOS = ["freezeTrace", "graceTrace", "durableTrace", "pairsTrace", "timeTrace", "beforeTrace"]
EXECUTION_SCENARIOS = ["durableTrace", "cachedTrace", "beforeTrace", "afterTrace", "abandonTrace",
                       "readOnlyTrace", "interruptedCheckTrace"]


def digest(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def registry_identity(keys):
    return {path.name: {"bytes": path.stat().st_size, "sha256": digest(path)}
            for path in sorted(keys.iterdir())
            if path.is_file() and (path.name == "manifest.json" or path.suffix in {".pk", ".vk"})}


def source_file_map(source):
    paths = run(["git", "ls-files", "--cached", "--others", "--exclude-standard"], source).splitlines()
    return {relative: digest(source / relative) for relative in sorted(set(paths))
            if (source / relative).is_file()}


def compiled_fixture_identity(output):
    messages = []
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except ValueError:
            continue
        if isinstance(message, dict):
            messages.append(message)
    tests = [message for message in messages
             if message.get("reason") == "compiler-artifact"
             and message.get("target", {}).get("name") == "shieldd_sdk_app"
             and message.get("profile", {}).get("test") and message.get("executable")]
    if len(tests) != 1:
        raise RuntimeError("fixture compile must identify exactly one actual app test executable")
    executable = Path(tests[0]["executable"]).resolve()
    target_root = executable.parent.parent.parent
    native = {}
    for message in messages:
        if message.get("reason") != "build-script-executed":
            continue
        directories = [Path(message["out_dir"])] if message.get("out_dir") else []
        directories.extend(Path(path.split("=", 1)[-1]) for path in message.get("linked_paths", []))
        for directory in directories:
            if directory.is_dir():
                directory = directory.resolve()
                if directory.is_relative_to(target_root):
                    candidates = directory.rglob("*")
                else:
                    # Hash only the explicitly linked library names here;
                    # never recursively walk a system-library search path.
                    names = [library.split("=", 1)[-1] for library in message.get("linked_libs", [])]
                    candidates = (directory / filename for name in names
                                  for filename in (f"lib{name}.a", f"lib{name}.so", f"lib{name}.dylib", f"{name}.lib"))
                for path in candidates:
                    if path.is_file() and path.suffix in {".a", ".o", ".so", ".dylib", ".dll", ".lib"}:
                        native[str(path.resolve())] = digest(path)
    if not native:
        raise RuntimeError("fixture compile did not bind actual native link artifacts")
    return {"path": str(executable), "sha256": digest(executable),
            "features": tests[0]["features"], "profile": tests[0]["profile"],
            "native_artifacts": native}


def linux(path):
    if isinstance(path, str) and path.startswith("/"):
        return path
    path = Path(path).resolve()
    if os.name == "nt":
        return "/mnt/" + path.drive[0].lower() + path.as_posix()[2:]
    return str(path)


def execute(args, name, *, cwd=ROOT, env=None, seconds=180, failure=False):
    """Use the root verifier's owned process group for every descendant."""
    if os.name == "nt":
        raise RuntimeError("run the entire security CLI inside Linux/WSL so cancellation owns all descendants")
    exports = {"QUINT_HOME": os.environ.get("SHIELDD_QUINT_HOME", linux(QUINT_HOME)), **(env or {})}
    words = ["env", *(f"{key}={value}" for key, value in exports.items()), *map(str, args)]
    result = run(words, cwd=cwd, timeout=seconds, check=False)
    output = result.stdout + result.stderr
    (WORK / f"{name}.log").write_text(output, encoding="utf-8")
    if not failure and result.returncode:
        raise RuntimeError(f"{name} failed ({result.returncode}); see {WORK / (name + '.log')}")
    if result.returncode in (124, 137):
        raise RuntimeError(f"{name} timed out; no assurance result")
    return result.returncode, output


def itf(value):
    if isinstance(value, dict):
        if "#bigint" in value:
            return int(value["#bigint"])
        if "#set" in value or "#tup" in value:
            return [itf(x) for x in value.get("#set", value.get("#tup"))]
        return {key: itf(item) for key, item in value.items() if not key.startswith("#")}
    if isinstance(value, list):
        return [itf(x) for x in value]
    return value


def check_model():
    cli = Path(os.environ.get("SHIELDD_QUINT_CLI", str(QUINT)))
    jar = Path(os.environ.get("SHIELDD_QUINT_HOME", str(QUINT_HOME))) / "apalache-dist-0.56.1/apalache/lib/apalache.jar"
    if not cli.is_file() or not jar.is_file():
        raise RuntimeError("install pinned Quint/Apalache per state/README.md first")
    if digest(jar) != JAR_SHA:
        raise RuntimeError("Apalache/TLC JAR identity differs from the qualified version")
    cli_sha = digest(cli)
    if cli_sha != QUINT_CLI_SHA:
        raise RuntimeError("selected Quint CLI differs from the qualified pinned CLI")
    quint = ["node", linux(cli)]
    _, version = execute([*quint, "--version"], "quint-version", seconds=30)
    if version.strip() != "0.32.0":
        raise RuntimeError("expected Quint 0.32.0")
    _, node = execute(["node", "--version"], "node-version", seconds=30)
    if int(node.strip().lstrip("v").split(".")[0]) < 18:
        raise RuntimeError("Quint requires Node >=18")
    _, java = execute(["java", "-version"], "java-version", seconds=30)
    model = ROOT / "state/snapshot.qnt"
    verify = [*quint, "verify", linux(model), "--main=snapshot", "--backend=tlc",
              "--tlc-config=" + linux(ROOT / "state/tlc.json"), "--invariant=invariant", "--verbosity=3"]
    _, output = execute(verify, "model", cwd=WORK, seconds=240)
    if "Model checking completed. No error has been found." not in output:
        raise RuntimeError("TLC did not report exhaustive completion of the finite model")
    counts = re.search(r"([\d,]+) states generated, ([\d,]+) distinct states found", output)
    if not counts:
        raise RuntimeError("TLC completion lacked state counts")
    tlc = re.search(r"TLC2 Version ([^\r\n]+)", output)
    fingerprint = re.search(r"with fp (\d+) and seed (-?\d+)", output)
    if not tlc or not fingerprint:
        raise RuntimeError("TLC completion lacked backend version or fingerprint parameters")
    # A relation mutation must violate the independent accepted-history invariant.
    original = model.read_text(encoding="utf-8")
    needle = "else if (matches.exists(p => p.epoch != st.epoch))"
    if original.count(needle) != 1:
        raise RuntimeError("epoch control mutation no longer matches model")
    mutant = WORK / "snapshot_mutant.qnt"
    mutant.write_text(original.replace(needle, "else if (false)"), encoding="utf-8")
    mutated = list(verify)
    mutated[3] = linux(mutant)
    code, counterexample = execute(mutated, "model-epoch-control", cwd=WORK, failure=True, seconds=120)
    if code == 0 or not re.search(r"Invariant .* is violated", counterexample):
        raise RuntimeError("model epoch control did not produce the intended invariant violation")
    _, tests = execute([*quint, "test", linux(model), "--main=snapshot", "--backend=typescript",
                       "--match=.*Trace", "--max-samples=1", "--out-itf=" + linux(WORK / "{test}_{seq}.itf.json")],
                      "traces", cwd=WORK, seconds=60)
    traces = []
    for sequence, name in enumerate(SCENARIOS):
        if f"{name} passed 1 test(s)" not in tests:
            raise RuntimeError(f"missing scenario execution: {name}")
        trace = json.loads((WORK / f"{name}_{sequence}.itf.json").read_text(encoding="utf-8"))
        if trace["#meta"].get("status") != "passed":
            raise RuntimeError("scenario trace did not pass")
        traces.append([{key: itf(state[key]) for key in ("op", "x", "y", "result", "s", "durable")}
                       for state in trace["states"]])
    (WORK / "traces.json").write_text(json.dumps(traces, indent=2), encoding="utf-8")
    return {"backend": "TLC", "tlc": tlc[1], "fingerprint_index": int(fingerprint[1]),
            "fingerprint_seed": fingerprint[2], "trace_backend": "typescript; deterministic action sequences",
            "quint": version.strip(), "quint_cli_sha256": cli_sha, "node": node.strip(), "java": java.strip(),
            "apalache": "0.56.1", "checker_sha256": JAR_SHA,
            "model_sha256": digest(model), "configuration_sha256": digest(ROOT / "state/tlc.json"),
            "npm_lock_sha256": digest(ROOT / "state/package-lock.json"),
            "generated_states": int(counts[1].replace(",", "")), "distinct_states": int(counts[2].replace(",", "")),
            "bounds": "10 transitions; heights1..4; times0..4; epochs0..2; two added assets; grace0/2",
            "workers": 1, "heap_mib": 1536, "deadlock_check": False,
            "epoch_control": "intended invariant violation", "traces_sha256": digest(WORK / "traces.json")}


def check_execution_model():
    """The same pinned toolchain checks the separate transaction lifecycle."""
    cli = Path(os.environ.get("SHIELDD_QUINT_CLI", str(QUINT)))
    quint = ["node", linux(cli)]
    model = ROOT / "state/execution.qnt"
    verify = [*quint, "verify", linux(model), "--main=execution", "--backend=tlc",
              "--tlc-config=" + linux(ROOT / "state/tlc.json"), "--invariant=invariant", "--verbosity=3"]
    _, output = execute(verify, "execution-model", cwd=WORK, seconds=240)
    counts = re.search(r"([\d,]+) states generated, ([\d,]+) distinct states found", output)
    if "Model checking completed. No error has been found." not in output or not counts:
        raise RuntimeError("execution model did not complete finite TLC exploration")
    original = model.read_text(encoding="utf-8")
    needle = "pure val applied: Effects = { spent: true, outputs: true, indexed: true }"
    if original.count(needle) != 1:
        raise RuntimeError("execution partial-effects control no longer matches")
    mutant = WORK / "execution_mutant.qnt"
    mutant.write_text(original.replace(needle, needle.replace("outputs: true", "outputs: false")), encoding="utf-8")
    mutated = list(verify)
    mutated[3] = linux(mutant)
    code, counterexample = execute(mutated, "execution-model-control", cwd=WORK, failure=True, seconds=120)
    if code == 0 or not re.search(r"Invariant .* is violated", counterexample):
        raise RuntimeError("partial-effect model control did not violate its invariant")
    _, output = execute([*quint, "test", linux(model), "--main=execution", "--backend=typescript",
                         "--match=.*Trace", "--max-samples=1", "--out-itf=" + linux(WORK / "execution_{test}_{seq}.itf.json")],
                        "execution-traces", cwd=WORK, seconds=60)
    traces = []
    for sequence, name in enumerate(EXECUTION_SCENARIOS):
        if f"{name} passed 1 test(s)" not in output:
            raise RuntimeError(f"missing execution trace: {name}")
        trace = json.loads((WORK / f"execution_{name}_{sequence}.itf.json").read_text(encoding="utf-8"))
        if trace["#meta"].get("status") != "passed":
            raise RuntimeError("execution trace did not pass")
        traces.append([{key: itf(state[key]) for key in
                       ("op", "result", "pending", "durable", "phase", "height", "committedHeight", "cache")}
                       for state in trace["states"]])
    trace_path = WORK / "execution-traces.json"
    trace_path.write_text(json.dumps(traces, indent=2), encoding="utf-8")
    return {"model_sha256": digest(model), "traces_sha256": digest(trace_path),
            "generated_states": int(counts[1].replace(",", "")),
            "distinct_states": int(counts[2].replace(",", "")),
            "bounds": "12 transitions; one transaction; committed heights1..3; atomic storage batches assumed",
            "partial_effect_control": "intended invariant violation"}


def check_rust(source):
    keys = Path(os.environ.get("SHIELDD_PARI_KEYS", source / "target/dev-pari-keys")).resolve()
    if not (keys / "manifest.json").is_file():
        raise RuntimeError("complete exact Pari registry required in SHIELDD_PARI_KEYS; replay remains blocked")
    registry_digest = digest(keys / "manifest.json")
    source_before = source_identity(source)
    source_files_before = source_file_map(source)
    registry_before = registry_identity(keys)
    environment = {"CARGO_BUILD_JOBS": "2", "RAYON_NUM_THREADS": "2", "SHIELDD_PARI_KEYS": linux(keys),
                   "SHIELDD_SNAPSHOT_TRACES": linux(WORK / "traces.json"),
                   "SHIELDD_EXECUTION_TRACES": linux(WORK / "execution-traces.json")}
    if "CARGO_TARGET_DIR" in os.environ:
        environment["CARGO_TARGET_DIR"] = linux(os.environ["CARGO_TARGET_DIR"])
    command = ["cargo", "test", "--locked", "--profile", "ci", "-p", "shieldd-sdk-app", "--lib"]
    _, rust = execute(["rustc", "--version"], "rust-version", cwd=source, seconds=30)
    _, cargo = execute(["cargo", "--version"], "cargo-version", cwd=source, seconds=30)
    cxx_command = os.environ.get("CXX", "c++")
    _, cxx = execute([cxx_command, "--version"], "cxx-version", cwd=source, seconds=30)
    _, compile_output = execute([*command, "--no-run", "--message-format=json"],
                                "runtime-fixture-compile", cwd=source, env=environment, seconds=1200)
    producer_build = compiled_fixture_identity(compile_output)
    dependencies = {"source": source_before, "source_files": source_files_before,
                    "registry": registry_before, "build": producer_build,
                    "cargo_lock_sha256": digest(source / "Cargo.lock"), "command": command,
                    "tools": {"rustc": rust.strip(), "cargo": cargo.strip(),
                              "cxx_command": cxx_command, "cxx_version": cxx.splitlines()[0]},
                    "environment": {name: os.environ.get(name) for name in
                                    ("CXX", "CXXFLAGS", "CC", "CFLAGS", "RUSTFLAGS",
                                     "CARGO_ENCODED_RUSTFLAGS", "RUSTC", "RUSTUP_TOOLCHAIN")}}
    dependency_digest = hashlib.sha256(json.dumps(dependencies, sort_keys=True).encode()).hexdigest()
    namespace = WORK / "fixtures" / dependency_digest
    namespace.mkdir(parents=True, exist_ok=True)
    fixture_directory = Path(tempfile.mkdtemp(prefix="attempt-", dir=namespace))
    fixture = fixture_directory / "transfer.bin"
    sidecar = fixture_directory / "producer.json"
    environment["SHIELDD_SNAPSHOT_TRANSFER"] = linux(fixture)
    runtime_source_bindings = []
    active_control = None

    def require_baseline_source():
        if source_identity(source) != source_before or source_file_map(source) != source_files_before:
            raise RuntimeError("runtime control requires byte-exact baseline source before mutation")

    def test(name, marker, log, failure=False):
        observed_source = source_identity(source)
        expected_files = dict(source_files_before)
        if active_control is not None:
            relative = Path(active_control["path"]).relative_to(source).as_posix()
            if expected_files.get(relative) != active_control["before_sha256"]:
                raise RuntimeError("runtime control does not match its baseline source file")
            expected_files[relative] = active_control["after_sha256"]
        if source_file_map(source) != expected_files:
            raise RuntimeError("runtime replay source differs outside the exact single-file mutation whitelist")
        if active_control is None and observed_source != source_before:
            raise RuntimeError("baseline runtime source changed before replay")
        if failure and active_control is None:
            raise RuntimeError("runtime mutation lacks an explicit source control binding")
        code, output = execute([*command, name, "--", "--ignored", "--nocapture", "--test-threads=1"],
                               log, cwd=source, env=environment, seconds=1200, failure=failure)
        if source_identity(source) != observed_source or source_file_map(source) != expected_files:
            raise RuntimeError("runtime source changed while its bound test was running")
        if not failure and (marker not in output or "1 passed" not in output):
            raise RuntimeError(f"{name}: expected executed passing test marker missing")
        runtime_source_bindings.append({"test": name, "log": log, "source": observed_source,
                                        "control": active_control, "fixture_dependency_sha256": dependency_digest})
        return code, output

    test("snapshot_host_trace_replay", "SNAPSHOT_REPLAY_OK", "runtime-traces")
    if fixture.exists() or sidecar.exists():
        raise RuntimeError("genuine fixture producer requires an absent fresh fixture")
    test("snapshot_transfer_cache_replay", "SNAPSHOT_CACHE_REPLAY_OK", "runtime-cache")
    if (source_identity(source) != source_before or registry_identity(keys) != registry_before
            or digest(producer_build["path"]) != producer_build["sha256"]
            or any(digest(path) != expected for path, expected in producer_build["native_artifacts"].items())):
        raise RuntimeError("genuine fixture dependencies changed during production")
    transfer_digest = digest(fixture)
    producer_receipt = {"dependencies": dependencies, "dependency_sha256": dependency_digest,
                        "fixture": str(fixture), "fixture_bytes": fixture.stat().st_size,
                        "fixture_sha256": transfer_digest,
                        "producer_test": "snapshot_transfer_cache_replay",
                        "producer_log_sha256": digest(WORK / "runtime-cache.log"),
                        "semantic_receipt": "actual witness_auth_build and verified delivery minted FullyVerified cache capability",
                        "reuse": "none; fresh unique attempt, existing shared fixture preserved"}
    with sidecar.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(producer_receipt, indent=2) + "\n")
    sidecar_digest = digest(sidecar)
    def execution_counts(output):
        summaries = re.findall(r"\bEXECUTION_REPLAY_OK[ \t]+([^\r\n]+)", output)
        if len(summaries) != 1:
            raise RuntimeError("execution replay must emit one coverage summary")
        pairs = [re.fullmatch(r"([a-z_]+)=(\d+)", field) for field in summaries[0].split()]
        if len(pairs) != 10 or any(pair is None for pair in pairs):
            raise RuntimeError("execution coverage summary must contain exactly ten integer fields")
        counts = dict(pair.groups() for pair in pairs)
        required = {"traces", "operations", "reopens", "interrupted_before", "interrupted_after",
                    "idle_checks", "ended_checks", "interrupted_before_checks",
                    "interrupted_after_checks", "cold_spent_checks"}
        if set(counts) != required or int(counts["traces"]) != len(EXECUTION_SCENARIOS) or any(int(value) <= 0 for value in counts.values()):
            raise RuntimeError("execution replay omitted required lifecycle/cache coverage")
        return {name: int(value) for name, value in counts.items()}

    _, execution_output = test("execution_host_trace_replay", "EXECUTION_REPLAY_OK", "runtime-execution")
    replay_counts = execution_counts(execution_output)
    _, retention = execute(["cargo", "test", "--locked", "--profile", "ci", "-p", "shieldd-sdk-compliance", "--lib",
                           "equal_timestamp_retention_exceeds_the_pruning_budget", "--", "--nocapture", "--test-threads=1"],
                          "runtime-retention", cwd=source, env=environment, seconds=1200)
    if "1 passed" not in retention:
        raise RuntimeError("70-pair retention/pruning test did not execute")

    # Restore on ordinary tool/test failures. Forced process-group termination can
    # bypass finally; the outer runner rejects a checkout left dirty in that case.
    path = source / "crates/core/component/compliance/src/admission.rs"
    before = path.read_bytes()
    needle = b"if snapshot.freeze_epoch != epoch {"
    if before.count(needle) != 1:
        raise RuntimeError("runtime epoch control no longer matches source")
    altered = before.replace(needle, b"if false && snapshot.freeze_epoch != epoch {")
    try:
        require_baseline_source()
        path.write_bytes(altered)
        active_control = {"name": "epoch", "path": str(path),
                          "before_sha256": hashlib.sha256(before).hexdigest(),
                          "after_sha256": hashlib.sha256(altered).hexdigest()}
        code, output = test("snapshot_transfer_cache_replay", "", "runtime-epoch-control", failure=True)
        if code == 0 or "SNAPSHOT_CACHE_REJECT: a cached proof crossed the freeze barrier" not in output or "test result: FAILED" not in output:
            raise RuntimeError("runtime epoch control did not detect actual cached delivery across freeze")
    finally:
        path.write_bytes(before)
        active_control = None
        if path.read_bytes() != before:
            raise RuntimeError("runtime control restoration failed")
        require_baseline_source()
    test("snapshot_transfer_cache_replay", "SNAPSHOT_CACHE_REPLAY_OK", "runtime-cache-restored")

    # Put the mixed-pair scenario first so this control must fail at the intended
    # unknown-pair assertion, rather than at an unrelated historical-age check.
    traces = json.loads((WORK / "traces.json").read_text(encoding="utf-8"))
    pairs = SCENARIOS.index("pairsTrace")
    mixed_traces = WORK / "mixed-control-traces.json"
    mixed_traces.write_text(json.dumps([traces[pairs], *traces[:pairs], *traces[pairs + 1:]]), encoding="utf-8")
    pair_needle = b"if *user == state.get_user_tree_root().await?\n            && *asset == state.get_asset_imt_root().await?"
    host_path = source / "crates/core/app/src/app/host.rs"
    rollback_needle = b"        self.app = app;\n        self.phase = HostExecutionPhase::Idle;\n        Ok(())\n    }\n\n    /// Drops"
    controls = [
        ("mixed-pair", path, pair_needle, pair_needle.replace(b"&&", b"||"),
         "operation=check expected=unknown actual=ok", linux(mixed_traces)),
        ("stale-rollback", host_path, rollback_needle, rollback_needle.replace(b"self.app = app;", b"drop(app);"),
         "SNAPSHOT_STATE trace=0 step=7", linux(WORK / "traces.json")),
    ]
    for name, control_path, needle, replacement, marker, trace_file in controls:
        original = control_path.read_bytes()
        # Git checkouts may use CRLF; mutate only the intended exact source span.
        if b"\r\n" in original:
            needle = needle.replace(b"\n", b"\r\n")
            replacement = replacement.replace(b"\n", b"\r\n")
        if original.count(needle) != 1:
            raise RuntimeError(f"runtime {name} control no longer matches source")
        try:
            require_baseline_source()
            control_path.write_bytes(original.replace(needle, replacement))
            active_control = {"name": name, "path": str(control_path),
                              "before_sha256": hashlib.sha256(original).hexdigest(),
                              "after_sha256": digest(control_path)}
            environment["SHIELDD_SNAPSHOT_TRACES"] = trace_file
            code, output = test("snapshot_host_trace_replay", "", f"runtime-{name}-control", failure=True)
            if code == 0 or marker not in output or "test result: FAILED" not in output:
                raise RuntimeError(f"runtime {name} control did not fail at its intended semantic assertion")
        finally:
            control_path.write_bytes(original)
            active_control = None
            environment["SHIELDD_SNAPSHOT_TRACES"] = linux(WORK / "traces.json")
            if control_path.read_bytes() != original:
                raise RuntimeError(f"runtime {name} control restoration failed")
            require_baseline_source()
    test("snapshot_host_trace_replay", "SNAPSHOT_REPLAY_OK", "runtime-traces-restored")
    # Preserve payload/index execution while omitting the real SCT append.
    # The success-path observer must detect the wrong root, not a build failure.
    sct_path = source / "crates/core/component/sct/src/component/tree.rs"
    sct_original = sct_path.read_bytes()
    sct_needle = (b"        // Record in the SCT\n        let mut tree = self.get_sct().await;\n"
                  b"        ensure_block_capacity(&tree, 1)?;\n"
                  b"        let position = tree.insert(tct::Witness::Forget, commitment)?;")
    sct_replacement = sct_needle.replace(
        b"tree.insert(tct::Witness::Forget, commitment)?",
        b'tree.position().context("execution control requires insert capacity")?')
    if b"\r\n" in sct_original:
        sct_needle = sct_needle.replace(b"\n", b"\r\n")
        sct_replacement = sct_replacement.replace(b"\n", b"\r\n")
    if sct_original.count(sct_needle) != 1:
        raise RuntimeError("execution SCT control no longer matches source")
    try:
        require_baseline_source()
        sct_path.write_bytes(sct_original.replace(sct_needle, sct_replacement))
        active_control = {"name": "omitted-SCT-append", "path": str(sct_path),
                          "before_sha256": hashlib.sha256(sct_original).hexdigest(),
                          "after_sha256": digest(sct_path)}
        code, output = test("execution_host_trace_replay", "", "runtime-execution-sct-control", failure=True)
        if code == 0 or "EXECUTION_SCT_APPEND" not in output or "test result: FAILED" not in output:
            raise RuntimeError("execution SCT control did not fail at its intended root assertion")
    finally:
        sct_path.write_bytes(sct_original)
        active_control = None
        if sct_path.read_bytes() != sct_original:
            raise RuntimeError("execution SCT control restoration failed")
        require_baseline_source()
    _, restored_output = test("execution_host_trace_replay", "EXECUTION_REPLAY_OK", "runtime-execution-restored")
    restored_counts = execution_counts(restored_output)
    _, restored_compile = execute([*command, "--no-run", "--message-format=json"],
                                 "runtime-fixture-restored-compile", cwd=source, env=environment, seconds=1200)
    restored_build = compiled_fixture_identity(restored_compile)
    if restored_build != producer_build:
        raise RuntimeError("restored actual app executable or native build identity differs from baseline producer")
    if (source_identity(source) != source_before or registry_identity(keys) != registry_before
            or digest(fixture) != transfer_digest or digest(sidecar) != sidecar_digest):
        raise RuntimeError("runtime source, registry, fresh transfer fixture or producer sidecar changed during replay")
    return {"rustc": rust.strip(), "profile": "ci", "test_threads": 1, "cargo_jobs": 2,
            "cxx_command": cxx_command, "cxx_version": cxx.splitlines()[0],
            "cxxflags": os.environ.get("CXXFLAGS", ""),
            "registry_manifest_sha256": registry_digest,
            "transfer_sha256": transfer_digest,
            "fixture_producer": producer_receipt, "fixture_sidecar_sha256": sidecar_digest,
            "runtime_source_bindings": runtime_source_bindings,
            "restored_build": restored_build,
            "epoch_control": "actual cached delivery accepted under mutated admission, rejected after restoration",
            "pair_control": "mixed pair wrongly accepted with disjunctive root comparison",
            "restore_control": "retained abandoned candidate detected after skipped rollback restore",
            "execution_sct_control": "omitted real SCT append detected by expected root/position comparison",
            "execution_replay_counts": replay_counts,
            "execution_restored_counts": restored_counts,
            "mutation_sha256": hashlib.sha256(altered).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--model-only", action="store_true", help="diagnostic model result; not full state replay")
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    try:
        model = check_model()
        execution = check_execution_model()
        runtime = None if args.model_only else check_rust(args.source.resolve())
        if digest(WORK / "traces.json") != model["traces_sha256"]:
            raise RuntimeError("generated traces changed during runtime replay")
        if digest(WORK / "execution-traces.json") != execution["traces_sha256"]:
            raise RuntimeError("execution traces changed during runtime replay")
        print(json.dumps({"outcome": "passed", "scope": "finite models only" if args.model_only else "finite snapshot and execution models with real runtime trace/cache/durability tests",
                          "model": model, "execution": execution, "runtime": runtime,
                          "limits": ["No Rust refinement proof or unbounded state theorem",
                                     "Cryptographic proof verification is modeled as an assumption; " +
                                     ("genuine-transfer runtime check unexecuted in model-only mode" if args.model_only else
                                      "one genuine transfer exercises cache integration"),
                                     "Cancellation and graceful database reopen, not arbitrary process/power-loss recovery",
                                     "One same-transaction replay, not distinct conflicting transactions or multi-action coverage",
                                     "No Bankd atomic settlement or all-family coverage"]}))
        return 0
    except (RuntimeError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"state: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
