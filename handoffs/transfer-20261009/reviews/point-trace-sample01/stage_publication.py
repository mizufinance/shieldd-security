"""Stage accepted sample sources separately from generated proof/evidence."""
import hashlib,json,shutil
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];REPO=ROOT/'work/shared-build-handoff';BASE=REPO/'handoffs/transfer-20261009';F=H/'frozen'
DEST=BASE/'sources/windows/point-trace-sample-20261009-01';REV=BASE/'reviews/point-trace-sample01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((F/'manifest.json').read_text());r=json.loads((F/'receipt.json').read_text());audit=json.loads((H/'packet-review01.json').read_text());review=json.loads((H/'opus55-review.json').read_text())
assert not review['is_error'] and 'claude-opus-5-5' in review['modelUsage'] and audit['exact_existing_full_types_and_axioms']==67
assert not DEST.exists() and not REV.exists();DEST.mkdir(parents=True);REV.mkdir(parents=True)
sources=[];evidence=[];omitted={}
for name,x in m['files'].items():
    assert sha(F/name)==x['sha256']
    if name.startswith(('review-audit-text/','resource-samples/')):omitted[name]=x;continue
    dst=DEST/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(F/name,dst)
    handwritten=name=='maintained-source/ConcretePointScalarRecurrence01.lean' or name.startswith('recipes/')
    (sources if handwritten else evidence).append(str(dst.relative_to(REPO)))
shutil.copyfile(F/'manifest.json',DEST/'producer-review-manifest.json');evidence.append(str((DEST/'producer-review-manifest.json').relative_to(REPO)))
for name in r['modules']:
    dst=REPO/'circuits/ShielddSecurity'/(name+'.lean');assert not dst.exists();shutil.copyfile(F/'maintained-source'/dst.name,dst)
    (sources if name=='ConcretePointScalarRecurrence01' else evidence).append(str(dst.relative_to(REPO)))
for name in ['opus55-review.json','review-disposition01.json','packet-review01.json','candidate-resource-audit01.json','candidate-reference-comparison02.json','canonical-context-manifest.json','audit_packet.py','run_review.py','stage_publication.py']:
    shutil.copyfile(H/name,REV/name);evidence.append(str((REV/name).relative_to(REPO)))
dst=DEST/'README.md';dst.write_text('''# Actual Point scalar sample

Six fresh modules and 67 complete declaration type/axiom audits establish eight additional regular actual Mathlib Point operations. The scalar prefix chain is 3 → 7 → 14 → 28 → 57 → 115, with output curve membership derived at every step. Two generic binary recurrence theorems hold for every AddMonoid and have no axioms. Other declarations use only standard propext, Classical.choice, and Quot.sound.

The parent rehashed all 89 producer entries, 71 canonical dependency references and two packet-new dependencies; reconstructed all six audited source wrappers; and parsed all 67 existing full type/axiom outputs. Selected candidate steps 2 through 6, exact base/field/runtime references, producer hashes and 32 integer-multiple data certificates were checked independently. All 182 recorded resource samples stayed above the existing stop thresholds. The fixed Windows limits remain 1536 MiB, 240 seconds per module, 300000 heartbeats and one heavy verifier. Claude Opus 5.5 high found no actionable mathematical, soundness, generator, or scope defect. The parent did not rerun Lean.

Together with the separately published initial pilot, ten regular operations are covered. The two initial infinity operations remain unrun; the remaining 357 operations, final scalar endpoint, nonzero/order/cardinality, native identity and full Transfer remain OPEN. Later step 251 and the final inverse cancellation need separate review. DecidableEq instances must be consistent during composition. Failed parser and universe-printer audit batches retain zero credit. No new negative control is claimed.

The producer records actual historical kernel checkouts separately from the frozen publication HEAD 8e55fc6550ca6ed0f4b7e81fa122f33c25fac4a0; inherited source identities agree. publication-manifest.json identifies shipped bytes. producer-review-manifest.json retains exact identities for successful type/axiom text and resource samples preserved locally. Raw logs, objects, caches, toolchains and composed workspaces are not published. This is a scoped checkpoint, with no final certification refresh.
''');evidence.append(str(dst.relative_to(REPO)))
public={str(p.relative_to(DEST)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(DEST.rglob('*')) if p.is_file()}
dst=DEST/'publication-manifest.json';dst.write_text(json.dumps({'schema':'parent-reviewed-eight-operation-point-sample-publication-v1','files':public,'omitted_local_successful_audit_text_and_resources':omitted,'producer_manifest_sha256':sha(F/'manifest.json'),'transport_payload_sha256':sha(H/'transport.xz'),'fresh_modules':6,'existing_full_type_axiom_audits':67,'new_regular_operations':8,'parent_kernel_runs':0,'full_transfer':'OPEN'},indent=2)+'\n');evidence.append(str(dst.relative_to(REPO)))
dst=BASE/'receipts/windows/point-trace-sample-20261009-01.json';dst.write_text(json.dumps({'schema':'reviewed-eight-operation-sample-publication-envelope-v1','producer_receipt':r,'producer_receipt_sha256':sha(F/'receipt.json'),'publication_manifest_sha256':sha(DEST/'publication-manifest.json'),'review_path':str(REV.relative_to(BASE)),'scope':'eight additional actual Point operations and scalar prefixes through115; remaining trace/order/cardinality/native OPEN','full_transfer':'OPEN'},indent=2)+'\n');evidence.append(str(dst.relative_to(REPO)))
(H/'publication-staging01.json').write_text(json.dumps({'sources':sources,'evidence':evidence,'canonical_modules':6,'packet_files':len(public),'omitted_audit_texts_and_resources':len(omitted)},indent=2)+'\n')
print(json.dumps({'canonical_modules':6,'packet_files':len(public),'omitted':len(omitted)}))
