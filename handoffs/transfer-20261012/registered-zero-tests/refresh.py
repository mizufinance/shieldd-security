"""Regenerate successful registry/word/header proofs and refresh compact evidence."""
from pathlib import Path
import argparse,hashlib,json,os
def pin(p):
    p=Path(p);return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
def checked(r):assert pin(r['path'])==r,r['path']
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--receipt-map',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists()
inputs=json.loads(a.receipt_map.read_bytes());templates=json.loads((root/'audit-names.json').read_bytes());pending=out.with_name(out.name+'.pending');pending.mkdir();reports=[];modules={}
for name,names in templates.items():
    rp=inputs[name];checked(rp);receipt=json.loads(Path(rp['path']).read_bytes())
    assert receipt['status']=='passed' and receipt['exit']==0 and receipt['stop'] is None and receipt['audit_error'] is None
    source=(root/'source/ShielddSecurity'/(name+'.lean')).read_bytes()
    generated=source+''.join('\nset_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n' for n in names).encode()
    assert len(generated)==receipt['source']['bytes'] and hashlib.sha256(generated).hexdigest()==receipt['source']['sha256']
    checked(receipt['source']);checked(receipt['stdout']);checked(receipt['stderr']);checked(receipt['dependency_manifest'])
    assert not Path(receipt['stderr']['path']).read_bytes()
    completion=json.loads((Path(rp['path']).parents[2]/'completion.json').read_bytes());assert completion['status']=='passed'
    assert completion['dependency_manifest']==receipt['dependency_manifest']
    for r in completion['final_files'].values():checked(r)
    plan=json.loads(Path(receipt['dependency_manifest']['path']).read_bytes())
    assert plan['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a' and plan['mathlib']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
    assert [r['name'] for r in receipt['audits']]==names
    for r in receipt['audits']:
        assert set(r['axioms'])<= {'propext','Quot.sound','Classical.choice'}
        assert hashlib.sha256(r['full_type'].encode()).hexdigest()==r['full_type_sha256']
    assert receipt['seconds']<=240 and receipt['peak_group_rss_bytes']<=4*1024**3
    assert all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in receipt['samples'])
    for r in receipt['objects'].values():checked(r)
    target=pending/'source/ShielddSecurity'/(name+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(generated)
    modules[name]=dict(source_sha256=receipt['source']['sha256'],receipt_sha256=rp['sha256'],object_sha256=receipt['objects']['.olean']['sha256'],stdout_sha256=receipt['stdout']['sha256'],seconds=receipt['seconds'],peak_group_rss_bytes=receipt['peak_group_rss_bytes'],selected_custom_modules=len(plan['selected']),reports=len(receipt['audits']))
    reports+=receipt['audits']
evidence=dict(status='passed',runtime_sha=plan['runtime_sha'],mathlib=plan['mathlib'],modules=modules,full_types_and_axioms=reports,refresh_sha256=pin(Path(__file__))['sha256'],reports=len(reports),full_transfer='OPEN',circuit_soundness='OPEN',total_legal_input_construction='OPEN',native_consequence='OPEN',certification=False,native_credit=0,
scope='Zero-test indicator/inverse hints survive the shared Boolean/word completion, with derived Boolean flags. The generic35-row registered block is satisfied under primitive one/control/LegalGuards inputs. This stage is not yet joined to HeaderSharedConstruction300 and does not reduce its11,939-row remainder. Other semantic bounds, all remaining truths and native correspondence are open.')
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps(dict(status='passed',modules=len(modules),reports=len(reports))))

