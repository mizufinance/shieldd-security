import hashlib,json,re,subprocess,sys,difflib
from pathlib import Path
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');P=R/'work/parent-call2-admission13';S=R/'work/mac-poseidon-width6-call2-13';T=S/'successor-source04';K=R/'outputs/mac-poseidon-width6-call2-13/kernel-successors01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
identity=lambda p:{'sha256':sha(p),'bytes':p.stat().st_size}
def check_manifest(p):
 v=json.loads(p.read_text())
 for n,e in v['entries'].items():
  path=R/n;assert path.is_file() and not path.is_symlink() and identity(path)==e,n
 return len(v['entries'])
assert sha(T/'repair-source-manifest01.json')=='880413edc0becf6295142bf6cf5393cb07771527e4127b6009596b7fa8f1e9a7'
sealed=check_manifest(T/'repair-source-manifest01.json')+check_manifest(T/'repair-source-envelope01.json')+check_manifest(S/'successor-source03/source-readiness-manifest01.json')
v=json.loads((T/'source-inventory01.json').read_text());old=json.loads((S/'successor-source03/source-inventory01.json').read_text());m=json.loads((T/'maintained-inventory01.json').read_text());om=json.loads((S/'successor-source03/maintained-inventory01.json').read_text())
assert {p.name for p in (T/'maintained').iterdir()}==set(m['maintained_files'])
for n,e in m['maintained_files'].items():assert identity(T/'maintained'/n)==e
assert [n for n in m['maintained_files'] if m['maintained_files'][n]!=om['maintained_files'][n]]==['generate_successors.py','build_successors_bounded.py']
deltas=[]
for n,e in v['modules'].items():
 assert identity(T/'project/ShielddSecurity'/(n+'.lean'))==identity(T/'generated01'/(n+'.lean'))==e
 assert identity(S/'project/ShielddSecurity'/(n+'.lean'))==old['modules'][n]
 if e!=old['modules'][n]:deltas.append(n)
assert deltas==['TransferPoseidonCall13Program01']
for n,e in v['prior_receipt_records'].items():assert identity(K/n)==e
records=[json.loads((K/n).read_text()) for n in v['prior_receipt_records']];assert len(records)==40 and len(list(K.glob('build-*.json')))==40
assert sum(r['status']=='passed' for r in records)==39
used=sum(r.get('seconds',0) for r in records if r.get('command_started'))+6.871448499994585
assert abs(used-221.6647063329874)<1e-8
for n,e in v['retained_prior_successors'].items():
 receipt=R/e['receipt_path'];r=json.loads(receipt.read_text());assert r['status']=='passed' and sha(receipt)==e['sha256']
 assert sha(T/'project/ShielddSecurity'/(n+'.lean'))==r['source_sha256'];assert sha(T/'project/.lake/build/lib/lean/ShielddSecurity'/(n+'.olean'))==r['object_sha256']
 for part in ['.olean.private','.olean.server','.ilean']:
  a=S/'project/.lake/build/lib/lean/ShielddSecurity'/(n+part);b=T/'project/.lake/build/lib/lean/ShielddSecurity'/(n+part)
  assert a.exists()==b.exists()
  if a.exists():assert identity(a)==identity(b)
 for name,d in r['frozen_imports'].items():
  if name in {'package','official_import_closure'}:continue
  assert sha(T/'project/ShielddSecurity'/(name+'.lean'))==d['source_sha256']
  obj=T/'project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean');assert sha(obj)==d['object_sha256']
  for part,digest in d['parts'].items():assert sha(obj.parent/part)==digest
for n,e in v['accepted_probes'].items():
 r=json.loads((R/e['receipt_path']).read_text());assert sha(R/e['receipt_path'])==e['receipt_sha256'] and r['status']=='passed'
 assert sha(T/'project/ShielddSecurity'/(n+'.lean'))==r['source_sha256'];assert sha(T/'project/.lake/build/lib/lean/ShielddSecurity'/(n+'.olean'))==r['object_sha256']
stop=json.loads((K/'kernel-stop01.json').read_text());f=stop['failed_module'];assert sha(R/f['log_path'])==f['log_sha256'] and sha(R/f['receipt_path'])==f['sha256'];assert f['proof_credit']==0
for n in ['readiness-controls01.json','cleanup-controls01.json']:
 c=json.loads((T/n).read_text());assert c['status']=='passed' and c['kernel_runs']==0
replay=P/'source-replay04'
subprocess.run([sys.executable,'-I','-B','-S',str(T/'maintained/verify_replay.py'),'--inventory',str(T/'maintained-inventory01.json'),'--inventory-sha256',sha(T/'maintained-inventory01.json'),'--source-inventory',str(T/'source-inventory01.json'),'--source-inventory-sha256',sha(T/'source-inventory01.json'),'--input',str(R/'outputs/mac-poseidon-width6-call2-13/compact-input02.json'),'--parameters',str(R/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381-wide.json'),'--topology',str(R/'outputs/mac-poseidon-width6-call2-13/successor-topology01.json'),'--output-dir',str(replay)],check=True)
changes={n:''.join(difflib.unified_diff((S/'successor-source03/maintained'/n).read_text().splitlines(True),(T/'maintained'/n).read_text().splitlines(True))) for n in ['generate_successors.py','build_successors_bounded.py']}
(P/'repair04-maintained-diff.txt').write_text(json.dumps(changes,indent=2))
report={'schema':'parent-call13-repair04-inspection','status':'passed','sealed_entries_rehashed':sealed,'source_delta':deltas,'unchanged_sources':44,'maintained_deltas':list(changes),'retained_successors':39,'retained_probe_modules':2,'prior_attempts':42,'prior_Lean_wall_seconds':used,'remaining_attempts':18,'remaining_wall_seconds':1200-used,'source_byte_replay_modules':45,'new_Lean_runs':0,'source_inventory_sha256':sha(T/'source-inventory01.json'),'maintained_inventory_sha256':sha(T/'maintained-inventory01.json'),'failure_preserved_zero_credit':True}
with (P/'parent-repair04-inspection01.json').open('x') as h:json.dump(report,h,indent=2)
print(json.dumps(report))
