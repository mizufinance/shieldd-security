"""Publish compact successful group replay evidence after exact source regeneration."""
from pathlib import Path
import argparse,hashlib,json,os,re
def pin(p):
    p=Path(p);h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def checked(r):assert pin(r['path'])==r,r['path']
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--execution',type=Path,required=True);ap.add_argument('--reproduction',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
execution=a.execution.resolve();out=a.output.resolve();assert not out.exists();completion=json.loads((execution/'completion.json').read_bytes());assert completion['status']=='passed'
checked(completion['dependency_manifest']);plan=json.loads(Path(completion['dependency_manifest']['path']).read_bytes());selection=json.loads((root/'selection.json').read_bytes());assert set(selection['selected'])==set(plan['selected'])
assert selection['runtime_sha']==plan['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert selection['mathlib']==plan['mathlib']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
for r in completion['final_files'].values():checked(r)
new={item['module']:item['receipt'] for item in completion['completed']};modules={};endpoints=[]
for name,row in plan['selected'].items():
    checked(row['source']);reproduced=a.reproduction.resolve()/'source/ShielddSecurity'/(name+'.lean')
    assert pin(reproduced)['sha256']==row['source']['sha256']==selection['selected'][name]['selected_source_sha256']
    receipt_pin=new.get(name,row.get('receipt'));assert receipt_pin is not None;checked(receipt_pin)
    receipt=json.loads(Path(receipt_pin['path']).read_bytes())
    compact=dict(source_sha256=row['source']['sha256'],source_bytes=row['source']['bytes'],receipt_sha256=receipt_pin['sha256'],fresh_selected_replay=name in new)
    # Slim guarded jobs expose complete audited types in their successful receipt.
    if 'stop' in receipt and 'peak_group_rss_bytes' in receipt and 'audits' in receipt and receipt.get('status')=='passed' and isinstance(receipt['audits'],list):
        checked(receipt['source']);assert receipt['source']==row['source']
        assert receipt['exit']==0 and receipt['stop'] is None and receipt['audit_error'] is None
        checked(receipt['stdout']);checked(receipt['stderr']);assert Path(receipt['stderr']['path']).read_bytes()==b''
        for obj in receipt['objects'].values():checked(obj)
        assert receipt['seconds']<=240 and receipt['peak_group_rss_bytes']<=4*1024**3
        assert all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in receipt['samples'])
        for report in receipt['audits']:
            assert set(report['axioms'])<= {'propext','Quot.sound','Classical.choice'}
            assert hashlib.sha256(report['full_type'].encode()).hexdigest()==report['full_type_sha256']
        compact.update(audits=[{k:r[k] for k in ['name','full_type_sha256','axioms']} for r in receipt['audits']],stdout_sha256=receipt['stdout']['sha256'],seconds=receipt['seconds'],peak_group_rss_bytes=receipt['peak_group_rss_bytes'],object_sha256=receipt['objects']['.olean']['sha256'])
        if name=='ConcreteCofactorModel01':endpoints=receipt['audits']
    else:
        compact['scope']='Inherited qualified Mac object/source; original receipt format retained locally. No new complete-declaration replay claim.'
    modules[name]=compact
assert len(endpoints)==8 and all('sorryAx' not in e['full_type'] for e in endpoints)
tmp=out.with_name(out.name+'.pending');tmp.mkdir()
evidence=dict(status='passed',scope='Concrete mathematical curve model, closed global exponent, traced base subgroup and cofactor implications. Native byte writer primitive remains explicit where used. No complete Transfer proof or native trace certification.',
runtime_sha=plan['runtime_sha'],mathlib=plan['mathlib'],selected_modules=len(modules),fresh_modules=sum(m['fresh_selected_replay'] for m in modules.values()),reports=sum(len(m.get('audits',[])) for m in modules.values()),modules=modules,endpoint_types_and_axioms=endpoints,
source_generator_sha256=pin(root/'generate.py')['sha256'],selection_sha256=pin(root/'selection.json')['sha256'],refresh_sha256=pin(Path(__file__))['sha256'],guard_sha256=pin(plan['files'][next(p for p in plan['files'] if p.endswith('/run_selected.py'))]['path'])['sha256'],
full_transfer='OPEN',circuit_soundness='OPEN',total_legal_input_construction='OPEN',native_consequence='OPEN',certification=False,native_credit=0)
(tmp/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(tmp,out)
print(json.dumps(dict(status='passed',selected_modules=evidence['selected_modules'],fresh_modules=evidence['fresh_modules'],reports=evidence['reports'],endpoints=len(endpoints))))

