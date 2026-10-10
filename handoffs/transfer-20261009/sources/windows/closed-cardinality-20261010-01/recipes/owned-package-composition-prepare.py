"""Fresh bounded owned composition; detailed retained identities remain externally pinned."""
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
FAILED = DIAG / 'transfer-base-order-owned-floor-20261010-01'
def pin(path):
    path = Path(path)
    with path.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
original = json.loads((FAILED / 'composition-review.json').read_text())
# No first-attempt admission credit: its final all-artifact guard rejected it.
assert sum(p.stat().st_size for p in FAILED.rglob('*') if p.is_file()) >= 64*1024**2
for r in original['frozen_original_receipts']: assert pin(r['path']) == r
for r in original['retained_original_owned']:
    assert pin(r['source']['path']) == r['source'] and pin(r['object']['path']) == r['object']
for r in original['selected']:
    assert pin(r['original']['path']) == r['original'] and pin(r['copy']['path']) == r['copy']
review = {'kind':original['kind'], 'recipe':pin(Path(__file__)),
    'retained_rejected_composition':pin(FAILED / 'composition-review.json'),
    'retained_rejected_recipe':pin(FAILED / 'prepare.py'),
    'rejection_reason':'First composition all-artifact guard rejected metadata duplication; no verifier launched and zero proof/admission credit.',
    'old_review':original['old_review'], 'shared_declaration_review':original['shared_declaration_review'],
    'prior_plan':original['prior_plan'], 'prior_events':original['prior_events'],
    'original_manifest':original['original_manifest'], 'original_complete':original['original_complete'],
    'original_exit':original['original_exit'], 'external_floor':original['external_floor'],
    'same_shared_declaration_bodies':True, 'direct_external_gaps':[], 'admission_ready':True,
    'kernel_credit':0, 'old_replays_relabelled':False,
    'scope':original['scope']+' Detailed historical qualification records remain pinned in the rejected composition; no failed guard is relabeled successful. This fresh composition independently verifies every selected original and records every new copied identity under unchanged64MiB cap.'}
project = ROOT / 'modules/ShielddSecurity'
selected = []
for r in original['selected']:
    dest = project / Path(r['original']['path']).name
    selected.append({'module':r['module'], 'original':r['original'],
        'copy':{'path':str(dest), 'bytes':r['original']['bytes'], 'sha256':r['original']['sha256']}})
review['selected'] = selected
encoded = json.dumps(review, separators=(',',':'), sort_keys=True)+'\n'
projected = sum(r['copy']['bytes'] for r in selected) + len(encoded.encode()) + Path(__file__).stat().st_size
assert projected + 4096 < 64*1024**2 and len(encoded.encode()) < 16*1024**2
project.mkdir(parents=True, exist_ok=False)
for r in selected:
    shutil.copyfile(r['original']['path'], r['copy']['path']); assert pin(r['copy']['path']) == r['copy']
(ROOT / 'composition-review.json').write_text(encoded, encoding='utf-8', newline='\n')
total = sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())
assert total == projected and total < 64*1024**2
print(json.dumps({'review':pin(ROOT / 'composition-review.json'), 'modules':len(selected), 'all_task_bytes':total,
    'task_cap_bytes':64*1024**2, 'kernel_credit':0}))
