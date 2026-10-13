"""Atomically qualify the authorization hash connections and retained incoming-key reduction."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys
def pin(p):
    p=Path(p);return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
verified={}
def checked(r):
    p=Path(r['path']);stamp=(p.stat().st_size,p.stat().st_mtime_ns)
    old=verified.get(str(p))
    if old is not None and old[0]==stamp:
        assert old[1]==r,r['path'];return
    assert pin(p)==r,r['path'];verified[str(p)]=(stamp,r)
json_cache={}
def read_json(p):
    p=Path(p)
    if str(p) not in json_cache:json_cache[str(p)]=json.loads(p.read_bytes())
    return json_cache[str(p)]
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--receipt-map',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists()
inputs=json.loads(a.receipt_map.read_bytes());templates=json.loads((root/'audit-names.json').read_bytes());pending=out.with_name(out.name+'.pending');pending.mkdir();reports=[];modules={}
generation={}
for folder in ['generator']:
    dest=pending/folder
    subprocess.run([sys.executable,'-B','-I','-S',str(root/folder/'generate.py'),str(dest)],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    for source in (dest/'source-root/ShielddSecurity').glob('*.lean'):
        assert source.stem not in generation
        generation[source.stem]=pin(source)
for name,names in templates.items():
    rp=inputs[name];checked(rp);receipt=json.loads(Path(rp['path']).read_bytes())
    assert receipt['status']=='passed' and receipt['exit']==0 and receipt['stop'] is None and receipt['audit_error'] is None
    sourcePath=root/'source/ShielddSecurity'/(name+'.lean')
    if not sourcePath.exists():sourcePath=Path(generation[name]['path'])
    source=sourcePath.read_bytes()
    generated=source
    assert len(generated)==receipt['source']['bytes'] and hashlib.sha256(generated).hexdigest()==receipt['source']['sha256']
    checked(receipt['source']);checked(receipt['stdout']);checked(receipt['stderr']);checked(receipt['dependency_manifest'])
    assert not Path(receipt['stderr']['path']).read_bytes()
    completion=read_json(Path(rp['path']).parents[2]/'completion.json')
    assert completion['status']=='passed'
    assert completion['dependency_manifest']==receipt['dependency_manifest']
    for r in completion['final_files'].values():checked(r)
    plan=read_json(receipt['dependency_manifest']['path'])
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
scope='Regulated commitment assertion3772 is constructed on the SAME retained assignment through exact selector rows, field input/point preservation, captured RNK hash and commitment hash semantics, and the independent legal regulated implication. Captured generator SDK identity and all full endpoints remain OPEN.')
coverage=json.loads((root/'coverage-base.json').read_bytes())
assert coverage['runtime_sha']==evidence['runtime_sha'] and len(set(coverage['known_positions']))==12914
assert 'ShielddSecurity.RegulatedConstruction542.legal_completed' in [r['name'] for r in reports]
evidence['generation']={'inputs':{str(file.relative_to(root)):pin(file)['sha256'] for folder in ['generator'] for file in sorted((root/folder).iterdir())},'sources':{n:{k:v for k,v in identity.items() if k!='path'} for n,identity in generation.items()}}
prior=set(coverage['known_positions']);positions={3772};known=prior|positions
assert len(positions)==1 and not (prior&positions) and len(known)==12915
evidence['conditional_assertion_coverage']=dict(previous_union=len(prior),positions=sorted(positions),new_positions=sorted(positions-prior),union=len(known),remaining=22816-len(known),total=22816,remaining_smaller_word_values=0,scope='ONE retained legal-input assignment; concrete source group operations. Full arbitrary-assignment soundness, total construction, computed public64 binding and native consequence remain OPEN.')
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps(dict(status='passed',modules=len(modules),reports=len(reports))))
