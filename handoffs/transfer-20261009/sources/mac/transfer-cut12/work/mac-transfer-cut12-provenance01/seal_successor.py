"""Append-only provenance successor binding the unchanged original seals."""
import hashlib,json
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-transfer-cut12-provenance01/attempt02'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
producer=R/'outputs/mac-transfer-cut12/publication-manifest01.json';envelope=R/'outputs/mac-transfer-cut12/seal-envelope01.json'
assert sha(producer)=='cf1511163550fb7e788df052bdef1837dd464f5cc7a0d6b17ab19f07f27f5a45'
assert sha(envelope)=='288dd9601abaf54a7418e5f6ec3c0011efb742ebea827cbf31dab0902d2363ce'
old={**json.loads(producer.read_text())['files'],**json.loads(envelope.read_text())['entries']}
for relative,identity in old.items():assert sha(R/relative)==identity['sha256']
verification=json.loads((O/'verification01.json').read_text());assert verification['status']=='passed' and verification['records']==61
records=json.loads((O/'full-audits-successor01.json').read_text())
assert len(records)==61 and all(hashlib.sha256(r['full_type'].encode()).hexdigest()==r['full_type_sha256'] for r in records)
checkpoint=S/'CHECKPOINT.md';assert not checkpoint.exists()
checkpoint.write_text(f'''# Cut12 provenance-only successor

Original producer `{sha(producer)}` and envelope `{sha(envelope)}` remain unchanged, including all83entrypaths/bytes. No Lean/proof/object/source or mathematical count changes.

Use outputs/mac-transfer-cut12-provenance01/attempt02/full-audits-successor01.json in place of original full-audits01.json for STRUCTURED audit text. Exactly legal and completed_materialized now exclude preceding linter diagnostics. Every one of61full_type hashes equals its existing successful build receipt. Wrapped axiom reports retained. Counts: root new closure3modules39audits; allstage7modules61audits, withprobes/checkercontrols separate. No new kernel credit.

Maintain extractor extract_audits.py; regeneration:

```sh
python3 -I -B -S extract_audits.py --root "$ORIGINAL_ROOT" --producer "$ORIGINAL_ROOT/outputs/mac-transfer-cut12/publication-manifest01.json" --envelope "$ORIGINAL_ROOT/outputs/mac-transfer-cut12/seal-envelope01.json" --output-dir "$FRESH_AUDIT_DIR"
```

Input raw success logs are immutable/local only, exactly hash-bound by existing receipts. This is an audit repair recipe, not a portable Lean generation recipe. Failed data-only first parser preserved; test_extractor.py verifies2positive+5refusals. Existing portable seven-source replay remains unchanged.

ACK published d6efed2121c93ac7ada701f6536fdb1afc5fb5f6. Workerquiescent, no proof/Git tasks launched. Parent review/publication pending; native/global/fullTransfer OPEN.
''')
paths=[S/'extract_audits.py',S/'test_extractor.py',S/'seal_successor.py',S/'parser-controls01.json',S/'failed-attempt01.json',checkpoint,O/'full-audits-successor01.json',O/'verification01.json']
paths.extend(p for p in (S/'source-history').rglob('*') if p.is_file())
files={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size,classification='provenance-only successor; no kernel credit') for p in paths}
p=S/'successor-manifest01.json';assert not p.exists()
p.write_text(json.dumps(dict(schema='cut12-provenance-only-successor-v1',original_producer_sha256=sha(producer),original_envelope_sha256=sha(envelope),original_entry_paths_rehashed=len(old),files=files,scope='Exact named signature extraction only; unchanged61audits/7modules and all proof bytes'),indent=2)+'\n')
print(json.dumps(dict(manifest=str(p),sha256=sha(p),files=len(files),corrected_audits_sha256=sha(O/'full-audits-successor01.json'),checkpoint_sha256=sha(checkpoint))))
