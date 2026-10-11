"""Independently review a name-only FeeFunding successor against accepted predecessor."""
from pathlib import Path
import json,re,hashlib,ast
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff';A=J.parent/'windows-raw-effects-review01';B=A/'packet01'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
prior=J.parent/'windows-readback-publication-review01/verify_endpoint.py';fn=next(n for n in ast.parse(prior.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(prior),'exec'))
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');ref=read(P/'context/prior-reference.json');parent=read(A/'endpoint-audit-review01.json')
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original'];assert len(b)==r['bytes']and sha(b)==r['sha256']
assert len(plan['targets'])==1;t=plan['targets'][0];b=(P/'source/ShielddSecurity/TransferRawEffectsSource01.lean').read_bytes();assert len(b)==t['source']['bytes']and sha(b)==t['source']['sha256'];assert all(t['source'][k]==t['predecessor_source'][k]for k in ['bytes','sha256'])
changes={'regulated_skips_volume_tail':'fee_funding_skips_volume_tail','regulated_success_retains_reshape_cache':'fee_funding_success_retains_reshape_cache'}
old=(B/'source/ShielddSecurity/TransferRawEffectsSource01.lean').read_text();new=b.decode().replace('\r\n','\n');expected=old
for a,z in changes.items():assert old.count(a)==3;expected=expected.replace(a,z)
assert expected==new
names=['ShielddSecurity.TransferRawEffectsSource01.'+n for n in re.findall(r'^#check @([\w.]+)\s*$',new,re.M)];assert names==t['audit_names']and len(names)==27
events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed'
reports=parse(P/'reports/fresh-27-complete-declarations.txt',names,result['audits']);log=(P/'reports/fresh-27-complete-declarations.txt').read_bytes();assert len(log)==result['stdout']['bytes']and sha(log)==result['stdout']['sha256']
for before,after in zip(parent['full_declarations'],reports):
 name=before['declaration'];sig=before['full_type']
 for a,z in changes.items():name=name.replace(a,z);sig=sig.replace(a,z)
 assert after==dict(declaration=name,full_type=sig,axioms=before['axioms'],full_type_sha256=sha(sig.encode()))
owned=read(P/'context/owned-composition-review.json')['selected'];oldowned=read(B/'context/owned-composition-review.json')['selected'];assert len(owned)==len(oldowned)==4
for a,z in zip(oldowned,owned):
 assert a['module']==z['module']and a['source']==z['source']and a['object']==z['object']
 assert all(a['copy'][k]==z['copy'][k]==z['object'][k]for k in ['bytes','sha256'])
assert read(P/'context/owned-composition-review.json')['inherited_public_reports']==read(B/'context/owned-composition-review.json')['inherited_public_reports']
assert plan['owned_imports']==[e['copy']for e in owned]and plan['external_floor']==read(B/'qualified/plan.json')['external_floor']
assert (P/'qualified/execute_bounded.py').read_bytes()==(B/'qualified/execute_bounded.py').read_bytes()and plan['pressure_limits']==read(B/'qualified/plan.json')['pressure_limits']
assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096']
assert result['command'][-1]==t['source']['path']and result['command'][-2]==result['objects'][0]['path']
runtime=W/'runtime-snapshot/crates/core/component/shielded-pool/src/volume_accumulator.rs';assert(P/'runtime/volume_accumulator.rs').read_bytes()==runtime.read_bytes();assert re.search(r'enum TransferProofContext\s*\{\s*Ordinary,\s*FeeFunding,?\s*\}',runtime.read_text())
assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes();pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
out=dict(kind='Independent name-only successor review against complete accepted predecessor; no Lean/native execution',fresh_modules=1,fresh_reports=27,full_declarations=reports,inherited_reports=57,manifest_entries=len(M['entries']),unchanged_full_type_reports=25,renamed_reports=changes,programs_and_contracts_unchanged=True,guard_unchanged=True,runtime_enum_exact=True,predecessor_review=dict(path=str(A/'endpoint-audit-review01.json'),bytes=(A/'endpoint-audit-review01.json').stat().st_size,sha256=sha((A/'endpoint-audit-review01.json').read_bytes())),context='ordinary=true is Ordinary; ordinary=false is FeeFunding; regulated disclosure is a separate input',full_transfer='OPEN')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='full_declarations'}))
