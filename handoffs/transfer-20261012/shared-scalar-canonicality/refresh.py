"""Atomically qualify fresh closed audits, reproduced sources and the shared join."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys

root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser()
ap.add_argument('--receipt-map',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args()
out=args.output.resolve()
assert not out.exists()
pending=out.with_name(out.name+'.pending')
pending.mkdir()

def pin(path):
    path=Path(path)
    return dict(path=str(path),bytes=path.stat().st_size,sha256=hashlib.sha256(path.read_bytes()).hexdigest())

def checked(identity):
    assert pin(identity['path'])==identity,identity['path']

sources={}
generations={}
for name in ['renames','rows']:
    destination=pending/('regenerated-'+name)
    subprocess.run([sys.executable,'-B','-I','-S',str(root/name/'generate.py'),'--output',str(destination)],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    generation=json.loads((destination/'generation.json').read_bytes())
    generations[name]=generation
    for module,record in generation.items():
        path=destination/'source-root/ShielddSecurity'/(module+'.lean')
        assert hashlib.sha256(path.read_bytes()).hexdigest()==record['sha256']
        sources[module]=path
for path in (root/'source/ShielddSecurity').glob('*.lean'):
    assert path.stem not in sources
    sources[path.stem]=path

inputs=json.loads(args.receipt_map.read_bytes())
reports=[]
modules={}
plans={}
verified_producers=set()
for name,identity in inputs.items():
    checked(identity)
    receipt=json.loads(Path(identity['path']).read_bytes())
    assert receipt['status']=='passed' and receipt['exit']==0 and receipt['stop'] is None and receipt['audit_error'] is None
    for key in ['source','stdout','stderr','dependency_manifest']:
        checked(receipt[key])
    assert not Path(receipt['stderr']['path']).read_bytes()
    assert sources[name].read_bytes()==Path(receipt['source']['path']).read_bytes()
    names=re.findall(r'#check @([A-Za-z0-9_.]+)',sources[name].read_text())
    assert names==[record['name'] for record in receipt['audits']]
    for record in receipt['audits']:
        assert set(record['axioms'])<= {'propext','Classical.choice','Quot.sound'}
        assert hashlib.sha256(record['full_type'].encode()).hexdigest()==record['full_type_sha256']
    assert receipt['seconds']<=240 and receipt['peak_group_rss_bytes']<=4*1024**3
    assert all(sample['free_memory_percent']>=15 and sample['free_disk_bytes']>=2*1024**3 for sample in receipt['samples'])
    producer=Path(identity['path']).parents[2]
    if producer not in verified_producers:
        completion=json.loads((producer/'completion.json').read_bytes())
        assert completion['status']=='passed' and completion['dependency_manifest']==receipt['dependency_manifest']
        for record in completion['final_files'].values():
            checked(record)
        verified_producers.add(producer)
    plan=json.loads(Path(receipt['dependency_manifest']['path']).read_bytes())
    assert plan['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
    assert plan['mathlib']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
    for record in receipt['objects'].values():
        checked(record)
    reports+=receipt['audits']
    plans[name]=plan
    modules[name]=dict(source_sha256=receipt['source']['sha256'],receipt_sha256=identity['sha256'],object_sha256=receipt['objects']['.olean']['sha256'],reports=len(receipt['audits']),seconds=receipt['seconds'],peak_group_rss_bytes=receipt['peak_group_rss_bytes'])

# The fresh root re-audits every public declaration in the 90 reused modules.
# Its successful producer verifies the closed source/object inventory before
# and after checking all417 full signatures and standard axiom closures.
audit_root='ScalarCanonicalRenames393'
root_audits={record['name']:record for record in reports if record['name'] in generations['renames'][audit_root]['audits']}
assert len(root_audits)==417
selected=plans[audit_root]['selected']
for name,generated in generations['renames'].items():
    row=selected[name]
    checked(row['source'])
    assert sources[name].read_bytes()==Path(row['source']['path']).read_bytes()
    if name!=audit_root:
        checked(row['object'])
        checked(row['receipt'])
        original=json.loads(Path(row['receipt']['path']).read_bytes())
        assert original['status']=='passed' and original['exit']==0 and original['stop'] is None and original['audit_error'] is None
        assert [record['name'] for record in original['audits']]==generated['audits']
        for record in original['audits']:
            assert root_audits[record['name']]==record
        modules[name]=dict(source_sha256=row['source']['sha256'],object_sha256=row['object']['sha256'],qualification='Fresh closed root417 full-type/axiom audit and unchanged verified source/object identities')

assert len(sources)==105 and len(modules)==105
assert len(reports)==520 and len({record['name'] for record in reports})==520
assert 'ShielddSecurity.ScalarCanonicalConstruction397.legal_completed' in {record['name'] for record in reports}
for name,path in sources.items():
    target=pending/'source/ShielddSecurity'/path.name
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(path.read_bytes())
coverage=json.loads((root/'coverage-base.json').read_bytes())
assert len(set(coverage['known_positions']))==11103
families=json.loads((root/'rows/families.json').read_bytes())
added={family['position']+offset for family in families for offset in [0,1]}
assert len(added)==18
known=set(coverage['known_positions'])|added
assert len(known)==11121 and all(0<=position<22816 for position in known)
evidence=dict(status='passed',runtime_sha=coverage['runtime_sha'],mathlib='c5ea00351c28e24afc9f0f84379aa41082b1188f',modules=modules,reports=520,full_types_and_axioms=reports,refresh_sha256=pin(Path(__file__))['sha256'],source_inventory={name:{key:value for key,value in pin(path).items() if key!='path'} for name,path in sources.items()},generators={name:{path.name:pin(path)['sha256'] for path in (root/name).iterdir() if path.is_file()} for name in ['renames','rows']},conditional_assertion_coverage=dict(previous_union=11103,new_positions=sorted(added-set(coverage['known_positions'])),union=len(known),remaining=22816-len(known),total=22816,remaining_smaller_word_values=0,scope='ONE assignment from independently legal TransferSem with all word bounds derived. Exact partial assertion union; neither full construction nor certification.'),scope='Nine remaining scalar-order comparisons retain exact captured row/port mappings, independent subgroup-scalar bounds and exact word bits. All18 original assertions follow on the same assignment. Fresh closed417-declaration audit preserves unchanged prior kernel proofs without recompiling them. Previous391 guarantees retained. All full endpoints remain OPEN.',full_transfer='OPEN',circuit_soundness='OPEN',total_legal_input_construction='OPEN',native_consequence='OPEN',native_credit=0,certification=False)
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n')
os.replace(pending,out)
print(json.dumps(dict(status='passed',modules=len(modules),reports=len(reports),union=len(known),remaining=22816-len(known))))
