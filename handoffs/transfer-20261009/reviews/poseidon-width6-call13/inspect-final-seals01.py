import hashlib,json,re
from pathlib import Path,PurePosixPath
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');P=R/'work/parent-call2-admission13';S=R/'work/mac-poseidon-width6-call2-13';T=S/'successor-source05';F=S/'final-result01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ident=lambda p:{'sha256':sha(p),'bytes':p.stat().st_size}
def manifest(p):
 v=json.loads(p.read_text())
 for n,e in v['entries'].items():
  rel=PurePosixPath(n);assert not rel.is_absolute() and '..' not in rel.parts
  f=R/n;assert f.is_file() and not f.is_symlink() and ident(f)=={k:e[k] for k in ['sha256','bytes']},n
 return len(v['entries'])
assert sha(F/'producer-manifest01.json')=='8c090b7d38a37ce6120352762b2cf2953cb58767e08f885a00a21f8fcde36146'
sealed=manifest(F/'producer-manifest01.json')+manifest(F/'post-seal-envelope01.json');prior=json.loads((F/'prior-seal-bindings01.json').read_text());old=0
for n,e in prior['manifests'].items():assert ident(R/n)==e;old+=manifest(R/n)
for n,e in prior['all_kernel_attempt_receipts'].items():assert ident(R/n)==e
worker=json.loads((F/'full-audits01.json').read_text())['exact_full_type_and_standard_axiom_records'];parent=json.loads((P/'parent-final-raw-audits01.json').read_text());own={x['declaration']:x for x in parent};assert len(own)==len(worker)==247
for x in worker:
 y=own[x['theorem']];assert x['module']==y['module'] and x['full_type']==y['full_type'] and x['axioms']==y['axioms'] and x['receipt_sha256']==y['receipt_sha256'] and x['log_sha256']==y['raw_log_sha256'];assert hashlib.sha256(x['full_type'].encode()).hexdigest()==x['full_type_sha256']
census=json.loads((F/'source-object-receipt-census01.json').read_text());assert len(census['modules'])==45
object_total=0
for n,x in census['modules'].items():
 p=R/x['receipt_path'];r=json.loads(p.read_text());assert ident(p)=={k:x[k] for k in ['sha256','bytes']};assert r['status']=='passed' and r['source_sha256']==x['source_sha256'] and r['object_sha256']==x['object_sha256']
 obj=T/'project/.lake/build/lib/lean/ShielddSecurity'/(n+'.olean');assert sha(obj)==x['object_sha256']
 object_total+=sum(p.stat().st_size for p in obj.parent.glob(n+'.*') if p.is_file())
root='TransferPoseidonCall13Proof01';pending=[root];seen=set()
while pending:
 name=pending.pop()
 if name in seen:continue
 seen.add(name);source=T/'project/ShielddSecurity'/(name+'.lean');assert source.is_file()
 pending.extend(re.findall(r'^import ShielddSecurity\.(\S+)',source.read_text(),re.M))
fresh=seen&set(census['modules']);inherited=seen-set(census['modules']);assert len(fresh)==43 and len(inherited)==98 and len(seen)==141
assert set(census['nonroot_fresh_modules'])==set(census['modules'])-fresh=={'TransferPoseidonCall13Checked01','TransferPoseidonCall13Controls01'}
assert sum(x['audits'] for n,x in census['modules'].items() if n in fresh)==230
result=json.loads((F/'result01.json').read_text());pr=json.loads((P/'parent-final-raw-inspection01.json').read_text());assert result['ALLLean_wall_seconds']==pr['used_ALLstage_Lean_wall_seconds'] and result['ALLattempts']==47 and result['ALLexact_full_types']==247 and result['actual_step_count']==313 and result['actual_selected_row_count']==417
assert object_total==result['owned45_current_object_part_bytes']==30951392
assert result['generated_source_bytes']==sum((T/'generated01'/(n+'.lean')).stat().st_size for n in census['modules'])==875550
assert result['source_plus_objects_bytes']==object_total+875550<536870912
scope=json.loads((F/'scope01.json').read_text());assert scope['controls']['total']==13 and scope['ALLstage_counts']['failed_attempts']==2
v={'status':'passed','new_manifest_envelope_entries_checked':sealed,'prior_manifest_entries_checked':old,'prior_manifests':6,'producer_all247_full_types_and_axioms_equal_independent_raw_extraction':True,'source_object_receipt_modules':45,'root_owned_closure':141,'root_fresh_modules':43,'root_inherited_modules':98,'root_audits':230,'nonroot_checked_controls_audits':17,'new_Lean_replay':0,'source_bytes':875550,'current_object_part_bytes':30951392,'scope_controls':13,'fullTransfer':'OPEN','Opus_review_pending':True}
with (P/'parent-final-seal-inspection01.json').open('x') as h:json.dump(v,h,indent=2);h.write('\n')
print(json.dumps(v))
