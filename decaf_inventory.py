#!/usr/bin/env python3
"""Expand the Decaf obligation matrix and inspect immutable source objects.

This inventory cannot certify anything: proof/binary evidence adapters and full
source/build closure are still required. Existing pilot receipts are not promoted.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib

import formal

MATRIX = formal.ROOT / "decaf/obligations.json"
TARGETS = {"x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"}
SOURCES = {"rust", "go", "shieldd", "rdsa", "orbis"}
PROFILES = {"rust-default", "rust-minimal", "go-normal", "go-purego",
            "shieldd-consumer", "rdsa-consumer", "orbis-consumer"}
FAMILIES = {"build-closure", "binary-qualification", "semantics", "field",
            "group", "compiled-traces", "consumer", "release"}
# Schema minima prevent accidental removal of agreed scope. The matrix owns
# concrete pins, profiles, dependency declarations and any additional obligations.
REQUIRED_PROPERTIES = {
    "build-closure": "source-locks resolved-features compiler-flags runtime-settings native-call-closure public-secret-classification",
    "binary-qualification": "instruction-coverage relocations-calls observer nonvacuity negative-controls",
    "semantics": "primitive-meaning concrete-interpretation memory-safety panic-safety termination",
    "field": "constants-primality add sub neg mul square select equality inverse sqrt-invsqrt montgomery parse serialize wide-reduction aliasing wrapper-conversions zero-heap-allocation",
    "group": "curve-invariants quotient-prime-order complete-formulas identity-exceptions scalar-action fixed-base variable-base multiscalar operator-routing encoding-canonicality encoding-roundtrip malformed-rejection map-hash-to-group extra-reachable-fields",
    "compiled-traces": "branch-address-termination arbitrary-permitted-points conversion-through-encoding runtime-closure noncircular-composition negative-controls",
    "consumer": "immutable-adoption actual-route-refinement key-validation transcript-domains rng-distribution protocol-reduction nonce-lifecycle adversarial-regressions",
    "release": "baseline-benchmarks clean-replay independent-correctness-review independent-simplicity-review",
}
CACHES = {"rust": (formal.CACHE / "decaf-rust.git", True),
          "go": (formal.CACHE / "decaf-inventory/go", False),
          "shieldd": (formal.CACHE / "decaf-inventory/shieldd", False),
          "rdsa": (formal.CACHE / "decaf-inventory/rdsa", False),
          "orbis": (formal.CACHE / "orbis", False)}


def unique(values, label):
    if not values or len(values) != len(set(values)):
        raise ValueError("empty or duplicate " + label)


def validate(matrix):
    if matrix.get("schema_version") != 1 or matrix.get("closure") != "open":
        raise ValueError("only open inventory schema 1 is supported; certification is not implemented")
    for key, expected in (("targets", TARGETS), ("sources", SOURCES)):
        if set(matrix[key]) != expected:
            raise ValueError("incomplete or unsupported " + key)
    if not PROFILES <= set(matrix["profiles"]):
        raise ValueError("required profile omitted")
    unique(matrix["targets"], "targets")
    if set(matrix["contracts"]) != {"decaf/proofs/protocol-contracts.md", "decaf/proofs/nonce-contracts.md"}:
        raise ValueError("required source-bound contract omitted or replaced")
    if not {"kernel", "extraction", "analysis", "compiler", "environment", "randomness", "cryptography", "physical"} <= set(matrix["assumptions"]):
        raise ValueError("required trust boundary omitted")
    for source in matrix["sources"].values():
        if not re.fullmatch(r"[0-9a-f]{40}", source["revision"]):
            raise ValueError("source requires an exact commit")
        if source["role"] not in {"inspection", "candidate"}:
            raise ValueError("adoption cannot be inferred from an inspection pin")
    for name, profile in matrix["profiles"].items():
        if profile["source"] not in SOURCES or profile["source"] != name.split("-", 1)[0]:
            raise ValueError("profile source does not match its required binding")
        if profile["default_features"] is not None and type(profile["default_features"]) is not bool:
            raise ValueError("default features must be explicit boolean or unresolved null")
        for key in ("features", "tags"):
            if profile[key] is not None and not isinstance(profile[key], list):
                raise ValueError("unresolved selections must be null")
    if (matrix["profiles"]["rust-default"]["default_features"] is not True or
            matrix["profiles"]["rust-minimal"]["default_features"] is not False):
        raise ValueError("default/minimal Cargo feature selection changed")
    names = [family["id"] for family in matrix["families"]]
    unique(names, "families")
    if set(names) != FAMILIES:
        raise ValueError("required obligation family omitted")
    dependencies = {}
    for family in matrix["families"]:
        unique(family["properties"], "properties")
        if not set(REQUIRED_PROPERTIES[family["id"]].split()) <= set(family["properties"]):
            raise ValueError("required property omitted")
        selection = ("libraries" if family["id"] in {"semantics", "field", "group"}
                     else "consumers" if family["id"] == "consumer" else "all")
        if family["profiles"] != selection:
            raise ValueError("required profile selection changed")
        if not set(family["assumptions"]) <= set(matrix["assumptions"]):
            raise ValueError("unknown assumption")
        if not set(family["depends_on"]) <= FAMILIES:
            raise ValueError("unknown dependency")
        if family["id"] == "field" and set(family.get("fields", [])) != {"fq", "fr"}:
            raise ValueError("required field omitted")
        if "fields" in family:
            unique(family["fields"], "fields")
        dependencies[family["id"]] = family["depends_on"]
    active, done = set(), set()

    def visit(name):
        if name in active:
            raise ValueError("circular obligation dependencies")
        if name in done:
            return
        active.add(name)
        for dependency in dependencies[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)

    for name in dependencies:
        visit(name)
    for replay in matrix["replays"].values():
        runner = replay["runner"]
        if not re.fullmatch(r"decaf_[a-z_]+\.py", runner) or not (formal.ROOT / runner).is_file():
            raise ValueError("invalid replay runner")


def expand(matrix):
    validate(matrix)
    rows = []
    families = {family["id"]: family for family in matrix["families"]}

    def inherited_assumptions(name):
        family = families[name]
        assumptions = set(family["assumptions"])
        for dependency in family["depends_on"]:
            assumptions.update(inherited_assumptions(dependency))
        return assumptions

    for family in matrix["families"]:
        for profile_id, profile in matrix["profiles"].items():
            consumer = profile["source"] in {"shieldd", "rdsa", "orbis"}
            if family["profiles"] == "libraries" and consumer:
                continue
            if family["profiles"] == "consumers" and not consumer:
                continue
            for target in matrix["targets"]:
                for field in family.get("fields", [None]):
                    for prop in family["properties"]:
                        parts = [family["id"], profile_id, target, *([field] if field else []), prop]
                        rows.append({"id": "/".join(parts), "family": family["id"],
                                     "profile": profile_id, "target": target, "field": field,
                                     "property": prop, "source": matrix["sources"][profile["source"]],
                                     "depends_on_families": family["depends_on"],
                                     "direct_assumptions": family["assumptions"],
                                     "transitive_assumptions": sorted(inherited_assumptions(family["id"])),
                                     "status": "blocked", "evidence": [],
                                     "reason": "complete source/build closure and property evidence required"})
    unique([row["id"] for row in rows], "expanded obligations")
    return rows


def inspect_source(source, cache, bare):
    prefix = ["git", "--git-dir=" + str(cache)] if bare else ["git", "-C", str(cache)]

    def git(*args):
        result = subprocess.run([*prefix, *args], capture_output=True, timeout=60,
                                env=dict(os.environ, GIT_NO_REPLACE_OBJECTS="1"))
        if result.returncode:
            raise ValueError(result.stderr.decode(errors="replace").strip())
        return result.stdout

    revision = source["revision"]
    if git("rev-parse", "--verify", revision + "^{commit}").decode().strip() != revision:
        raise ValueError("not the requested immutable commit")
    tree = git("ls-tree", "-rz", "--full-tree", revision)
    files, dependencies = [], []
    manifests = {"Cargo.toml", "Cargo.lock", "go.mod", "go.sum", "rust-toolchain", "rust-toolchain.toml"}
    for entry in tree.split(b"\0"):
        if not entry:
            continue
        metadata, path_bytes = entry.split(b"\t", 1)
        mode, kind, oid = metadata.decode().split()
        path = path_bytes.decode()
        if Path(path).name in manifests:
            files.append({"path": path, "git_object": oid, "kind": kind, "mode": mode})
            if kind != "blob" or mode not in {"100644", "100755"}:
                raise ValueError("manifest is not a regular source blob: " + path)
            body = git("cat-file", "blob", oid).decode()
            dependencies.extend(dependency_records(path, body))
    return {"status": "inspected", "revision": revision,
            "git_tree_listing_sha256": hashlib.sha256(tree).hexdigest(),
            "manifests": files, "decaf_dependency_records": dependencies,
            "resolved_build_closure": False,
            "note": "immutable Git objects only; features, toolchains and deployment not inferred"}


def dependency_records(path, body):
    """Record declarations and locked identities without resolving features."""
    records = []
    name = Path(path).name
    if name == "Cargo.lock":
        for package in tomllib.loads(body).get("package", []):
            if package["name"].startswith("decaf377"):
                records.append({"path": path, "kind": "cargo-lock", "package": package})
    elif name == "Cargo.toml":
        def walk(value, location):
            if not isinstance(value, dict):
                return
            for key, entry in value.items():
                if key in {"dependencies", "dev-dependencies", "build-dependencies"} and isinstance(entry, dict):
                    for alias, declaration in entry.items():
                        package = declaration.get("package", alias) if isinstance(declaration, dict) else alias
                        if package.startswith("decaf377"):
                            records.append({"path": path, "kind": "cargo-declaration",
                                            "section": location + [key], "alias": alias,
                                            "package": package, "declaration": declaration})
                else:
                    walk(entry, location + [key])
        walk(tomllib.loads(body), [])
    elif name in {"go.mod", "go.sum"}:
        for number, line in enumerate(body.splitlines(), 1):
            if "decaf377" in line:
                records.append({"path": path, "kind": name, "line": number, "text": line.strip()})
    return records


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(dir=path.parent, prefix=".inventory-", suffix=".tmp")
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            json.dump(value, output, indent=2)
            output.write("\n")
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["status", "list-replays"])
    args = parser.parse_args()
    matrix = json.loads(MATRIX.read_text())
    rows = expand(matrix)
    if args.action == "list-replays":
        print(json.dumps(matrix["replays"], indent=2))
        return 0
    with formal.exclusive_lock():
        inspected = {}
        for name, source in matrix["sources"].items():
            try:
                inspected[name] = inspect_source(source, *CACHES[name])
            except (ValueError, OSError, subprocess.TimeoutExpired) as error:
                inspected[name] = {"status": "blocked", "detail": str(error)}
        report = {"status": "blocked", "completed": False, "full_certification": False,
                  "inventory_generated": True, "matrix_sha256": formal.file_digest(MATRIX),
                  "runner_sha256": formal.file_digest(Path(__file__)),
                  "contract_hashes": {name: formal.file_digest(formal.ROOT / name) for name in matrix["contracts"]},
                  "claim": matrix["claim"], "assumptions": matrix["assumptions"],
                  "source_inspection": inspected, "obligations": rows,
                  "detail": "inventory is open; no evidence acceptance or certification adapter exists"}
        path = formal.WORK / "decaf-inventory/report.json"
        atomic_json(path, report)
    print(json.dumps({"status": "blocked", "obligations": len(rows), "report": str(path)}))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
