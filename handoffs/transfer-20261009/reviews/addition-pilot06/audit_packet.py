"""Read-only packet/source/existing stdout audit; no fresh kernel verification."""
import datetime
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument("--packet", type=Path, default=HERE / "frozen")
parser.add_argument("--repo", type=Path, default=HERE.parents[1] / "work/shared-build-handoff")
args = parser.parse_args()
PACKET = args.packet.resolve()
REPO = args.repo.resolve()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((PACKET / "manifest.json").read_text())
receipt = json.loads((PACKET / "receipt.json").read_text())
inputs = json.loads((PACKET / "inputs/manifest.json").read_text())
for name, expected in manifest["files"].items():
    path = PACKET / name
    assert sha(path) == expected["sha256"]
    assert path.stat().st_size == expected["bytes"]
assert sha(PACKET / "inputs/manifest.json") == receipt["source_manifest_sha256"]
assert receipt["actual_publication_checkout_head"] == "0c270fdf940dc929e642a8bffaf9ae63fe5b7250"
assert receipt["runtime_sha"] == "844389ee069e1fb2e576708842d0b389b4d9a44a"
assert receipt["mathlib_sha"] == "c5ea00351c28e24afc9f0f84379aa41082b1188f"
assert receipt["lean_version"] == "4.30.0"
assert receipt["batch_actual_exit"] == 0
recipe = receipt["recipe"]
assert recipe["threads"] == 1 and recipe["memory_MiB"] == 1536
assert recipe["finite_seconds_per_module"] == 240
assert recipe["admission_wait_seconds"] == 60
assert sha(PACKET / "recipes/root-windows-addition-pilot-20261009-06.ps1") == recipe["guard_sha256"].lower()
assert sha(PACKET / "recipes/audit-windows-addition-pilot-20261009-06.py") == recipe["audit_sha256"].lower()
dependencies = json.loads((PACKET / "dependency-resolution.json").read_text())
for dependency in dependencies:
    assert sha(REPO / dependency["canonical_repository_reference"]) == dependency["original_source_sha256"]
    assert sha(PACKET / "canonical-dependencies" / (dependency["name"] + ".lean")) == dependency["original_source_sha256"]

results = []
audited_names = []
for module, names in inputs["expected_theorems_by_module"].items():
    source = PACKET / "maintained-source" / (module + ".lean")
    candidate = PACKET / "audited-source" / (module + ".lean")
    body = source.read_text(encoding="utf-8-sig")
    assert sha(source) == inputs["sources"][module]["sha256"]
    end = list(re.finditer(r"(?m)^end\s+([\w.]+)\s*$", body))[-1].start()
    checks = "".join(f"\nset_option pp.all true in\n#check @{name}\n#print axioms {name}\n" for name in names)
    reconstructed = body[:end] + checks + body[end:]
    assert reconstructed.encode() == candidate.read_bytes()
    assert sha(candidate) == inputs["audited_candidates"][module]
    leaf = receipt["modules"][module]
    audit = leaf["audit"]
    assert leaf["actual_exit"] == 0 and audit["full_types_checked"]
    assert audit["original_source_sha256"] == sha(source)
    assert audit["candidate_sha256"] == sha(candidate)
    assert audit["audits"] == len(names) == len(audit["axioms"])
    stdout = PACKET / "review-audit-text" / (module + ".txt")
    assert sha(stdout) == leaf["stdout_sha256"]
    text = stdout.read_text()
    assert "error:" not in text and "sorryAx" not in text
    observed = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
    observed += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    assert sorted(name for name, _ in observed) == sorted(audit["axioms"])
    for name, axioms in observed:
        values = [value.strip() for value in axioms.split(",") if value.strip()]
        assert set(values) <= {"propext", "Classical.choice", "Quot.sound"}
        assert sorted(values) == sorted(audit["axioms"][name])
        signatures = re.findall(r"^@?" + re.escape(name) + r"\s*:[\s\S]*?(?=^'" + re.escape(name) + r"')", text, re.M)
        assert len(signatures) == 1, name
        audited_names.append(name)
    elapsed = datetime.datetime.fromisoformat(leaf["end"]) - datetime.datetime.fromisoformat(leaf["start"])
    assert 0 < elapsed.total_seconds() <= 240
    results.append({"module": module, "source_sha256": sha(source), "candidate_sha256": sha(candidate), "declarations": len(names), "seconds": elapsed.total_seconds()})
assert len(results) == receipt["fresh_modules"] == 2
assert len(audited_names) == len(set(audited_names)) == receipt["declaration_audits"] == 17
result = {"kind": "source-packet-and-existing-successful-stdout-review", "files_rehashed": len(manifest["files"]), "dependencies_rehashed": len(dependencies), "fresh_worker_modules": results, "exact_existing_stdout_types_and_axioms": 17, "kernel_rerun": False, "full_transfer": "OPEN", "scope": receipt["proved_scope"], "open": receipt["open"], "unverified_candidates": receipt["other_maintained_sources"], "new_negative_control_credit": 0}
(HERE / "packet-review01.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"status": "passed", "files": len(manifest["files"]), "dependencies": len(dependencies), "existing_stdout_audits": len(audited_names)}))
