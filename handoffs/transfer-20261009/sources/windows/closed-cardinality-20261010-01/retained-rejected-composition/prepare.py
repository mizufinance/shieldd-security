"""Pin and copy the exact reviewed owned closure; identity qualification, no new Lean credit."""
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-implementation-20261002/windows-point-order-20261009-01-kernel'
def pin(path):
    path = Path(path)
    with path.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
old_review_path = DIAG / 'transfer-base-order-import-review-20261010-01/review.json'
old = json.loads(old_review_path.read_text())
shared_path = DIAG / 'transfer-base-order-shared-source-review-20261010-02/review.json'
shared = json.loads(shared_path.read_text())
assert shared['all_same_declaration_source_body'] and len(shared['modules']) == 42
prior = DIAG / 'transfer-concrete-cardinality-join-20261010-01'
prior_plan = json.loads((prior / 'plan.json').read_text())
prior_done = [json.loads(x) for x in (prior / 'events.jsonl').read_text().splitlines() if json.loads(x)['event'] == 'attempt_finished']
assert len(prior_done) == 1 and prior_done[0]['result']['status'] == 'passed'
current = prior_plan['owned_imports'] + prior_done[0]['result']['objects']
objects = {Path(r['path']).stem:r for r in current}
manifest = json.loads((OLD / 'manifest.json').read_text(encoding='utf-8-sig'))
assert (OLD / 'exit.txt').read_text(encoding='utf-8-sig').strip() == '0'
reused = {r['name']:r for r in manifest['reused']}
receipt_pins = []
for path, sha in manifest['frozen_import_receipts'].items():
    r = pin(path); assert r['sha256'] == sha; receipt_pins.append(r)
retained = []
for name, r in old['owned'].items():
    stem = name.split('.')[-1]
    assert pin(r['source']['path']) == r['source'] and pin(r['object']['path']) == r['object']
    if stem in reused:
        evidence = reused[stem]
        assert r['source']['sha256'] == evidence['source_sha256'] and r['object']['sha256'] == evidence['object_sha256']
        qualification = {'kind':'exact_original_reused_pair', 'manifest':pin(OLD / 'manifest.json')}
    else:
        assert stem in manifest['order']
        audit = OLD / stem / 'audit.json'
        a = json.loads(audit.read_text(encoding='utf-8-sig'))
        assert a['full_types_checked'] and a['audits'] > 0
        assert all(set(axioms) <= {'propext','Classical.choice','Quot.sound'} for axioms in a['axioms'].values())
        assert r['source']['sha256'] == manifest['audited_candidates'][stem] == a['candidate_sha256']
        assert (OLD / stem / 'exit.txt').read_text(encoding='utf-8-sig').strip() == '0'
        qualification = {'kind':'retained_completed_original_named_module', 'audit':pin(audit),
            'stdout':pin(OLD / stem / 'stdout.txt'), 'exit':pin(OLD / stem / 'exit.txt')}
    retained.append({'module':name, **r, 'original_qualification':qualification,
        'selected_current_shared_object': objects.get(stem)})
    if stem not in objects: objects[stem] = r['object']
assert not old['floor_gaps']
project = ROOT / 'modules/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
selected = []
for name, source in sorted(objects.items()):
    assert pin(source['path']) == source
    dest = project / (name + '.olean'); shutil.copyfile(source['path'], dest)
    alias = pin(dest); assert alias['bytes'] == source['bytes'] and alias['sha256'] == source['sha256']
    selected.append({'module':'ShielddSecurity.'+name, 'original':source, 'copy':alias})
review = {'kind':'EXACT_OWNED_SOURCE_OBJECT_IMPORT_COMPOSITION', 'recipe':pin(Path(__file__)),
    'old_review':pin(old_review_path), 'shared_declaration_review':pin(shared_path),
    'prior_plan':pin(prior / 'plan.json'), 'prior_events':pin(prior / 'events.jsonl'),
    'original_manifest':pin(OLD / 'manifest.json'), 'original_complete':pin(OLD / 'complete.txt'),
    'original_exit':pin(OLD / 'exit.txt'), 'frozen_original_receipts':receipt_pins,
    'retained_original_owned':retained, 'selected':selected,
    'external_floor':pin(DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json'),
    'same_shared_declaration_bodies':True, 'direct_external_gaps':[], 'admission_ready':True,
    'kernel_credit':0, 'old_replays_relabelled':False,
    'scope':'Exact old qualified owned source/object pairs retained; all42 shared declaration source bodies match the current separately passed prerequisites and their current objects are selected. Old320 additional objects explicitly copied and identified by preserved receipts. The complete current external floor is separately pinned. No old module is claimed newly replayed, no hash is a semantic refinement claim; a new named closed join remains required.'}
(ROOT / 'composition-review.json').write_text(json.dumps(review, separators=(',',':'), sort_keys=True)+'\n')
total = sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())
assert total < 64*1024**2 and (ROOT / 'composition-review.json').stat().st_size < 16*1024**2
print(json.dumps({'review':pin(ROOT / 'composition-review.json'), 'modules':len(selected),
    'all_task_bytes':total, 'task_cap_bytes':64*1024**2, 'kernel_credit':0}))
