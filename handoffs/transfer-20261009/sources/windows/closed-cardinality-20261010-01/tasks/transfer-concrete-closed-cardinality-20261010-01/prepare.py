"""Prepare a new closed join consuming explicitly copied immutable owned imports."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-concrete-cardinality-join-20261010-01'
POOL = DIAG / 'transfer-base-order-owned-floor-20261010-02'
def pin(path):
    path = Path(path)
    with path.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path':str(path), 'bytes':path.stat().st_size, 'sha256':sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
done = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines() if json.loads(x)['event']=='attempt_finished']
assert len(done)==1 and done[0]['result']['status']=='passed'
pool = json.loads((POOL / 'composition-review.json').read_text())
assert pool['admission_ready'] and pool['same_shared_declaration_bodies'] and pool['kernel_credit']==0
assert sum(p.stat().st_size for p in POOL.rglob('*') if p.is_file()) < 64*1024**2
history = json.loads(Path(pool['retained_rejected_composition']['path']).read_text())
owned = [r['copy'] for r in pool['selected']]
for r in owned: assert pin(r['path']) == r
source = ROOT / 'handwritten/ConcreteClosedCardinality01.lean'
text = source.read_text()
names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) and len(names)==4
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
dest = project / source.name; shutil.copyfile(source,dest)
body = (PRIOR / 'execute_bounded.py').read_text()
start = body.index('def own_cache(accepted_objects):')
end = body.index('\n\ndef import_resolution', start)
replacement = '''def own_cache(accepted_objects):
    project = ROOT / 'project' / 'ShielddSecurity'
    # This plan imports one explicitly copied, immutable owned package floor.
    # All its files were fully charged in its completed composition task.
    # The current task charges every new target source/output, with all existing
    # byte, output-reservation, object-format, time and memory guards unchanged.
    pool_record = PLAN['owned_import_pool']
    verify([pool_record])
    pool = json.loads(Path(pool_record['path']).read_text())
    if not pool['admission_ready'] or pool['kernel_credit'] != 0:
        raise RuntimeError('Unqualified owned package floor')
    pinned = {os.path.normcase(str(Path(r['copy']['path']).resolve())):r['copy'] for r in pool['selected']}
    pool_root = Path(pool_record['path']).parent / 'modules' / 'ShielddSecurity'
    actual_pool = set()
    for p in pool_root.rglob('*'):
        if p.is_file():
            if p.is_symlink() or pool_root.resolve() not in p.resolve().parents:
                raise RuntimeError('Linked/escaped owned package floor')
            actual_pool.add(os.path.normcase(str(p.resolve())))
    if actual_pool != set(pinned): raise RuntimeError('Owned package floor keyset changed')
    initial = {os.path.normcase(str(Path(r['path']).resolve())):r for r in PLAN['owned_imports']}
    if initial != pinned: raise RuntimeError('Plan differs from selected owned floor')
    accepted = {os.path.normcase(str(Path(r['path']).resolve())):r for r in accepted_objects}
    if not set(pinned) <= set(accepted): raise RuntimeError('Owned floor omitted')
    expected = {os.path.normcase(str(Path(t['source']['path']).resolve())) for t in PLAN['targets']}
    for key in set(accepted) - set(pinned):
        if project.resolve() not in Path(key).parents:
            raise RuntimeError('Unexpected extra accepted object location')
        expected.add(key)
    actual = set()
    for path in project.rglob('*'):
        if path.is_file():
            if path.is_symlink() or project.resolve() not in path.resolve().parents:
                raise RuntimeError('Unexpected linked/escaped own-cache input')
            actual.add(os.path.normcase(str(path.resolve())))
    if actual != expected:
        raise RuntimeError('Own cache keyset changed; future/unqualified artifacts are forbidden')
    verify(accepted_objects)
'''
body = body[:start]+replacement+body[end:]
ast.parse(body)
runner=ROOT/'execute_bounded.py'; runner.write_text(body,encoding='utf-8',newline='\n')
plan['owned_imports']=owned
plan['owned_import_pool']=pin(POOL/'composition-review.json')
plan['lean_path']=[str(POOL/'modules'),str(ROOT/'project')]+plan['lean_path'][1:]
plan['targets']=[{'module':source.stem,'source':pin(dest),'predecessor_source':pin(source),
    'imports':re.findall(r'^import\s+([A-Za-z0-9_.]+)',text,re.M),'audit_names':names}]
records=[pin(runner),pin(Path(__file__)),pin(source),pin(PRIOR/'execute_bounded.py'),pin(PRIOR/'plan.json'),
    pin(PRIOR/'events.jsonl'),done[0]['result']['stdout'],pin(POOL/'prepare.py'),pin(POOL/'composition-review.json')]
records += [pin(pool[k]['path']) for k in ['old_review','shared_declaration_review','retained_rejected_composition','retained_rejected_recipe']]
records += history['frozen_original_receipts']
for r in history['retained_original_owned']:
    records += [r['source'],r['object']]
    records += [v for v in r['original_qualification'].values() if isinstance(v,dict) and 'sha256' in v]
records += [r['original'] for r in pool['selected']] + owned
plan['pins'] += records
# Keep every distinct immutable record; only exact repeated records are removed.
unique={}
for r in plan['pins']:
    key=r['path']; assert key not in unique or unique[key]==r; unique[key]=r
plan['pins']=list(unique.values())
plan['kind']='FRESH_CLOSED_ACTUAL_BASE_ORDER_CARDINALITY_AND_GLOBAL_EXPONENT_JOIN'
plan['scope']='New named closed actual base-order/cardinality/global8r exponent join, consuming all curve-side results and retained exact previous base trace/order objects. No base-order/cardinality premise intended. Old362 modules are retained inputs and are not claimed newly replayed; all42 shared declaration bodies match selected current passed objects. Native and fullTransfer remain open.'
plan['repairs']='Explicit immutable owned package floor first in LEAN_PATH permits new small target artifacts under unchanged64MiB per task and conservative output reservation. Floor creation independently charges all383 copied import objects66.48MB, verifies source/object provenance and unchanged shared declaration bodies. own_cache verifies exact pool and plan keysets and copied bytes, rejects linked/escaped/extra files, and keeps strict new target source/output keyset. All other guards unchanged; no cap/resource increase.'
(ROOT/'plan.json').write_text(json.dumps(plan,separators=(',',':'),sort_keys=True)+'\n',encoding='utf-8',newline='\n')
(ROOT/'review.json').write_text(json.dumps({'plan':pin(ROOT/'plan.json'),'runner':pin(runner),'audits':4,
    'owned_pool':plan['owned_import_pool'],'source':pin(source),'scope':plan['scope'],'runner_change':plan['repairs']},indent=2)+'\n')
print(json.dumps({'plan':pin(ROOT/'plan.json'),'runner':pin(runner),'audits':4,'owned_modules':len(owned)}))
