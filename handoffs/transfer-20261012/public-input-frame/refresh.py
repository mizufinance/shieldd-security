from pathlib import Path
import argparse,hashlib,json,os
def pin(p):
    p=Path(p);return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
def checked(r):assert pin(r['path'])==r,r['path']
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--receipt-map',type=Path,required=True);ap.add_argument('--reproduction',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists()
receipts=json.loads(a.receipt_map.read_bytes());assert len(receipts)==59;records={};types=[]
for name,rp in receipts.items():
    checked(rp);r=json.loads(Path(rp['path']).read_bytes());assert r['status']=='passed' and r['exit']==0 and r['stop'] is None and r['audit_error'] is None
    checked(r['source']);checked(r['stdout']);checked(r['stderr']);checked(r['dependency_manifest']);assert not Path(r['stderr']['path']).read_bytes()
    reproduced=a.reproduction.resolve()/'source-root/ShielddSecurity'/(name+'.lean');assert pin(reproduced)['sha256']==r['source']['sha256']
    for obj in r['objects'].values():checked(obj)
    assert r['seconds']<=240 and r['peak_group_rss_bytes']<=4*1024**3
    assert all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in r['samples'])
    for report in r['audits']:
        assert set(report['axioms'])<= {'propext','Classical.choice','Quot.sound'}
        assert hashlib.sha256(report['full_type'].encode()).hexdigest()==report['full_type_sha256']
    records[name]=dict(source_sha256=r['source']['sha256'],receipt_sha256=rp['sha256'],object_sha256=r['objects']['.olean']['sha256'],seconds=r['seconds'],peak_group_rss_bytes=r['peak_group_rss_bytes'],audits=[{k:p[k] for k in ['name','full_type_sha256','axioms']} for p in r['audits']])
    if name=='SharedPublicFrame301':
        completion=json.loads((Path(rp['path']).parents[2]/'completion.json').read_bytes());assert completion['status']=='passed'
        for record in completion['final_files'].values():checked(record)
        plan=json.loads(Path(r['dependency_manifest']['path']).read_bytes());types=r['audits']
assert len(types)==8 and sum(len(r['audits']) for r in records.values())==66
pending=out.with_name(out.name+'.pending');pending.mkdir()
evidence=dict(status='passed',runtime_sha=plan['runtime_sha'],mathlib=plan['mathlib'],modules=records,reports=66,endpoint_types_and_axioms=types,generator_sha256=pin(root/'generate.py')['sha256'],leaves_sha256=pin(root/'leaves.json')['sha256'],refresh_sha256=pin(Path(__file__))['sha256'],scope='All Boolean and word hint write sets exclude original public column22737. The same completed shared assignment preserves that public input and links declared public column1 to it. This does not prove the computed statement agrees with independent public64 or establish remaining assertion truth.',full_transfer='OPEN',certification=False,native_credit=0)
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps(dict(status='passed',modules=59,reports=66,endpoints=8)))

