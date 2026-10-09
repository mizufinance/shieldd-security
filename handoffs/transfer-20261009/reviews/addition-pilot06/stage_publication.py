"""Stage immutable reviewed sources/portable records; leave large audit text local."""
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT / "work/shared-build-handoff"
BASE = REPO / "handoffs/transfer-20261009"
PACKET = HERE / "frozen"
DEST = BASE / "sources/windows/addition-pilot-20261009-06"
REVIEWS = BASE / "reviews/addition-pilot06"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

if DEST.exists():
    previous = json.loads((DEST / "publication-manifest.json").read_text())
    for name, identity in previous["files"].items():
        assert sha(DEST / name) == identity["sha256"]
    shutil.rmtree(DEST)
if REVIEWS.exists():
    for name in ["opus55-review.json", "review-disposition01.json", "packet-review01.json", "audit_packet.py"]:
        assert sha(REVIEWS / name) == sha(HERE / name)
    shutil.rmtree(REVIEWS)
review = json.loads((HERE / "opus55-review.json").read_text())
assert not review["is_error"] and "claude-opus-5-5" in review["modelUsage"]
audit = json.loads((HERE / "packet-review01.json").read_text())
assert audit["exact_existing_stdout_types_and_axioms"] == 17
manifest = json.loads((PACKET / "manifest.json").read_text())
for name, identity in manifest["files"].items():
    assert sha(PACKET / name) == identity["sha256"]

DEST.mkdir(parents=True)
REVIEWS.mkdir(parents=True)
omitted = {}
for name, identity in manifest["files"].items():
    if name.startswith("review-audit-text/"):
        omitted[name] = identity
        continue
    target = DEST / name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(PACKET / name, target)
shutil.copyfile(PACKET / "manifest.json", DEST / "producer-review-manifest.json")
for name in ["opus55-review.json", "review-disposition01.json", "packet-review01.json", "audit_packet.py", "stage_publication.py"]:
    shutil.copyfile(HERE / name, REVIEWS / name)
for name in ["EdwardsAdditionPilot01", "ConcretePointAdditionPilot01"]:
    target = REPO / "circuits/ShielddSecurity" / (name + ".lean")
    if target.exists():
        assert target.read_bytes() == (PACKET / "maintained-source" / target.name).read_bytes()
    shutil.copyfile(PACKET / "maintained-source" / target.name, target)

(DEST / "README.md").write_text("# Scoped Point addition pilot\n\nTwo fresh Windows modules establish generic Edwards addition closure and the concrete Mathlib negation, identity and inverse images. The parent verified the transported sources, 68 canonical dependency references, reconstructed audited sources and all 17 existing type/axiom outputs. Claude Opus 5.5 found no defect in this scope. No parent kernel rerun occurred.\n\nGeneral addition, StandardCurveModel, point order/cardinality and native joins remain open. Other maintained sources retain the statuses in receipt.json. Failed attempts have zero credit.\n\npublication-manifest.json identifies shipped producer files; producer-review-manifest.json also identifies two successful audit text files retained locally and omitted from publication. Canonical dependency sources are referenced by exact hashes. The local parent audit script needs those omitted texts for stdout rechecking; public readers can inspect the full source and reported audit census. No full Transfer certification or atomic certification refresh occurred.\n")
public = {str(p.relative_to(DEST)): {"sha256": sha(p), "bytes": p.stat().st_size} for p in sorted(DEST.rglob("*")) if p.is_file()}
envelope = {"kind": "portable-publication-manifest-generated-from-frozen-review-packet", "files": public, "omitted_local_successful_audit_text": omitted, "producer_manifest_sha256": sha(PACKET / "manifest.json"), "transport_payload_sha256": sha(HERE / "transport-payload.gz"), "audited_worker_modules": 2, "parent_existing_stdout_audits": 17, "kernel_rerun": False, "full_transfer": "OPEN", "scope": "Concrete Mathlib negation and identity/inverse addition images; general addition/order/native OPEN. Other maintained candidates retain receipt statuses, not addition06 credit."}
(DEST / "publication-manifest.json").write_text(json.dumps(envelope, indent=2) + "\n")
receipt = json.loads((PACKET / "receipt.json").read_text())
portable = {"kind": "publication-envelope-with-producer-receipt", "producer_receipt": receipt, "producer_receipt_sha256": sha(PACKET / "receipt.json"), "publication_manifest_sha256": sha(DEST / "publication-manifest.json"), "review": "reviews/addition-pilot06", "full_transfer": "OPEN"}
(BASE / "receipts/windows/addition-pilot-20261009-06.json").write_text(json.dumps(portable, indent=2) + "\n")
print(json.dumps({"staged_files": len(public), "local_audit_texts_omitted": len(omitted), "canonical_modules": 2}))
