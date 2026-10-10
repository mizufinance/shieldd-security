"""Independently inspect a staged scoped checkpoint. Never mutates Git or evidence."""
from pathlib import Path
import argparse,hashlib,json,sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
V=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--candidate',required=True);ap.add_argument('--repository',required=True);ap.add_argument('--output',required=True);a=ap.parse_args()
C=Path(a.candidate).resolve();R=Path(a.repository).resolve()
def load(p):return json.loads(p.read_bytes())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
st=load(C/'staging01.json');plan=load(V/'publication-plan03.json')
files={p.relative_to(C).as_posix():p for p in C.rglob('*') if p.is_file()}
assert set(files)==set(st['files'])|{'staging01.json'}
assert set(st['maintained']).isdisjoint(st['generated'])
assert set(st['maintained'])|set(st['generated'])==set(st['files'])
for n,e in st['files'].items():
 p=files[n];assert not p.is_symlink() and p.stat().st_size==e['bytes'] and sha(p)==e['sha256']
 assert not any(k in p.relative_to(C).parts for k in ['.lake','__pycache__','node_modules'])
 assert p.suffix not in {'.log','.olean','.ir','.ilean','.xz','.pyc','.sqlite'}
for src,e in plan['entries'].items():
 p=Path(src);q=C/e['destination'];assert p.stat().st_size==q.stat().st_size==e['bytes']
 assert sha(p)==sha(q)==e['sha256'] and p.read_bytes()==q.read_bytes()
 assert e['destination'] in st[e['commit_class']]
modules=[p for n,p in files.items() if n.startswith('circuits/ShielddSecurity/')]
assert len(modules)==st['canonical_modules']==57 and all(p.suffix=='.lean' for p in modules)
assert all(not (R/p.relative_to(C)).exists() for p in modules)
for n in ['TransferPoseidonCall14Checked01.lean','TransferPoseidonCall14Controls01.lean']:
 assert not (C/'circuits/ShielddSecurity'/n).exists() and not (R/'circuits/ShielddSecurity'/n).exists()
B=C/'handoffs/transfer-20261009';pub=load(B/'sources/mac/poseidon-call14/publication-manifest01.json');rec=load(B/'receipts/mac/poseidon-call14.json')
assert sha(B/'sources/mac/poseidon-call14/publication-manifest01.json')==rec['publication_manifest_sha256']
for src,e in plan['entries'].items():
 q=pub['producer_mapping'][src];assert q==dict(published_path=e['destination'],sha256=e['sha256'],bytes=e['bytes'])
for n,e in pub['files'].items():assert files[n].stat().st_size==e['bytes'] and sha(files[n])==e['sha256']
d=rec['acceptance'];assert d['status']=='accepted_scoped_checkpoint' and d['actual_review_returncode']==0 and d['full_Transfer']=='OPEN'
review=Path(d['actual_final_Opus_review']['path']);assert sha(review)==d['actual_final_Opus_review']['sha256']
j=load(review);assert j.get('is_error') is False and 'claude-opus-5-5' in j.get('modelUsage',{})
assert pub['producer_manifest_sha256']==d['final_manifest_sha256']=='a1860ff75f5117b55d5366c5aa96e0a1358830df831118fb0469065f35bbb995'
assert d['publication_plan_sha256']==sha(V/'publication-plan03.json')
assert load(R/'shieldd.lock')['sha']==pub['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
out=dict(status='PASS_EXACT_STAGED_PUBLICATION_IDENTITIES_ONLY',files=len(files),original_selected_entries=len(plan['entries']),canonical_new_modules=57,maintained=len(st['maintained']),generated=len(st['generated']),raw_logs_objects_caches_DB_published=False,parent_Lean_runs=0,full_Transfer='OPEN',base_sha=st['base_sha'])
with Path(a.output).open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(out))
