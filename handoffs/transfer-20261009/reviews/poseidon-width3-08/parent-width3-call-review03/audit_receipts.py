"""Audit immutable successful width3 receipts and existing logs without Lean."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STAGE = ROOT / "work/mac-poseidon-width3-08"
OUT = ROOT / "outputs/mac-poseidon-width3-08"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


accepted = []
failures = []
for path in sorted(OUT.glob("build-*.json")):
    receipt = json.loads(path.read_text())
    name = receipt["module"]
    if not (name.startswith("TransferPoseidonWidth3") or name in {"PoseidonHash3OneBlock08", "PoseidonCallTraversal03"}):
        continue
    if receipt["status"] != "passed":
        failures.append({"receipt": path.name, "status": receipt["status"], "credit": 0})
        continue
    source = STAGE / "project/ShielddSecurity" / (name + ".lean")
    log = path.with_suffix(".log")
    assert sha(source) == receipt["source_sha256"], name
    assert sha(log) == receipt["log_sha256"], name
    assert receipt["exit"] == 0
    assert receipt["lean_heap_limit_MiB"] == 2048
    assert receipt["timeout_seconds"] == 240
    assert receipt["seconds"] <= 240
    assert receipt["process_group_rss_limit_bytes"] == 4 * 1024**3
    assert receipt["peak_group_rss_bytes"] <= 4 * 1024**3
    assert receipt["minimum_memory_free_percent"] >= 15
    assert receipt["minimum_disk_free_bytes"] >= 2 * 1024**3
    assert "-j1" in receipt["command"] and "-M2048" in receipt["command"]
    assert receipt["frozen_imports"]["mathlib_revision"] == "c5ea00351c28e24afc9f0f84379aa41082b1188f"
    for filename, identity in receipt["guard_sources_sha256"].items():
        assert sha(STAGE / filename) == identity
    text = log.read_text()
    assert "error:" not in text and "sorryAx" not in text
    observed = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
    observed += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    assert sorted(name for name, _ in observed) == sorted(receipt["expected_axiom_names"])
    for theorem, axioms in observed:
        values = {value.strip() for value in axioms.split(",") if value.strip()}
        assert values <= {"propext", "Classical.choice", "Quot.sound"}, theorem
    for theorem, identity in receipt["full_signature_sha256"].items():
        hits = re.findall(r"^@?" + re.escape(theorem) + r"\s*:[\s\S]*?(?=^'" + re.escape(theorem) + r"')", text, re.M)
        assert len(hits) == 1
        assert hashlib.sha256(hits[0].strip().encode()).hexdigest() == identity
    assert len(receipt["full_signature_sha256"]) == len(receipt["expected_signature_names"])
    assert receipt["axiom_audits"] == len(observed)
    accepted.append({"module": name, "receipt": path.name, "receipt_sha256": sha(path), "source_sha256": sha(source), "log_sha256": sha(log), "audits": len(observed), "full_types": len(receipt["full_signature_sha256"]), "seconds": receipt["seconds"], "rss_bytes": receipt["peak_group_rss_bytes"]})
assert len({record["module"] for record in accepted}) == len(accepted)
frozen = json.loads((HERE / "source-manifest.json").read_text())
matches = []
for name, identity in frozen.items():
    source = Path(identity["source"])
    matches.append({"name": name, "frozen_sha256": identity["sha256"], "current_sha256": sha(source), "unchanged": sha(source) == identity["sha256"]})
result = {"kind": "dated-existing-source-receipt-and-log-audit", "kernel_rerun": False, "accepted": accepted, "modules": len(accepted), "audits": sum(record["audits"] for record in accepted), "full_types": sum(record["full_types"] for record in accepted), "failures_and_running_no_credit": failures, "frozen_source_matches": matches, "full_transfer": "OPEN"}
attempt = 1
while (HERE / f"receipt-audit{attempt:02d}.json").exists():
    attempt += 1
(HERE / f"receipt-audit{attempt:02d}.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"modules": result["modules"], "audits": result["audits"], "source_review_deltas": [record["name"] for record in matches if not record["unchanged"]]}))
