"""Review transported full declarations, source contracts, exact imports and guard."""
from pathlib import Path
import json,re,hashlib,ast,difflib
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
prior=J.parent/'windows-readback-publication-review01/verify_endpoint.py';tree=ast.parse(prior.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(prior),'exec'))
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');pins={}
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original'];assert len(b)==r['bytes']and sha(b)==r['sha256'];pins[r['path']]=r
assert len(plan['targets'])==1;t=plan['targets'][0];b=(P/'source/ShielddSecurity/TransferRawEffectsSource01.lean').read_bytes();assert len(b)==t['source']['bytes']and sha(b)==t['source']['sha256'];assert all(t['source'][k]==t['predecessor_source'][k]for k in ['bytes','sha256'])
text=b.decode();names=['ShielddSecurity.TransferRawEffectsSource01.'+n for n in re.findall(r'^#check @([\w.]+)\s*$',text,re.M)];assert names==t['audit_names']and len(names)==27
public=re.findall(r'^(?:def|theorem|structure|inductive) ([\w.]+)',text,re.M);assert names==['ShielddSecurity.TransferRawEffectsSource01.'+n for n in public]
assert re.findall(r'^import ([\w.]+)',text,re.M)==t['imports']==['ShielddSecurity.TransferNullifierBatchSource01'];assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',text)
events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed'
reports=parse(P/'reports/fresh-27-complete-declarations.txt',names,result['audits']);raw=(P/'reports/fresh-27-complete-declarations.txt').read_bytes();assert len(raw)==result['stdout']['bytes']and sha(raw)==result['stdout']['sha256']
assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==t['source']['path']and result['command'][-2]==result['objects'][0]['path']
A=G/'handoffs/transfer-20261009/sources/windows/raw-state-program-20261011-01';V=G/'handoffs/transfer-20261009/sources/windows/reader-vector-20261011-01';B=J.parent/'windows-nullifier-batch-review01/packet01'
rawreview=read(A/'parent-review/endpoint-audit-review01.json');vectorreview=read(V/'parent-review/endpoint-audit-review01.json');batchreview=read(J.parent/'windows-nullifier-batch-review01/endpoint-audit-review01.json')
audits={e['declaration']:{k:e[k]for k in ['axioms','full_type_sha256']}for e in rawreview['full_declarations']+rawreview['inherited_declarations']+vectorreview['full_declarations']+batchreview['full_declarations']};assert len(audits)==57
owned=read(P/'context/owned-composition-review.json');assert owned['inherited_public_reports']==audits and len(owned['selected'])==4
objects={'TransferStateDelta':rawreview['custom_import']['object'],'TransferRawStateProgram01':read(A/'review.json')['compiler_result']['objects'][0],'TransferNullifierReaderVector01':read(V/'review.json')['compiler_result']['objects'][0],'TransferNullifierBatchSource01':read(B/'review.json')['compiler_result']['objects'][0]}
for e in owned['selected']:
 n=e['module'];doc=B if n=='TransferNullifierBatchSource01'else V if n=='TransferNullifierReaderVector01'else A;source=(doc/'source/ShielddSecurity'/(n+'.lean')).read_bytes();assert len(source)==e['source']['bytes']and sha(source)==e['source']['sha256'];assert all(e['object'][k]==objects[n][k]==e['copy'][k]for k in ['bytes','sha256'])
assert plan['owned_imports']==[e['copy']for e in owned['selected']]
ref=read(P/'context/inherited-reference.json')
for key,doc in [('raw',A),('vector',V),('batch',B)]:
 m=(doc/'manifest.json').read_bytes();assert len(m)==ref[key]['manifest']['bytes']and sha(m)==ref[key]['manifest']['sha256']
Q=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01';floor=Q/'context/core-external-floor.json';pin=ref['core_floor']['original'];assert len(floor.read_bytes())==pin['bytes']and sha(floor.read_bytes())==pin['sha256']and plan['external_floor']==pin
assert(P/'qualified/execute_bounded.py').read_bytes()==(Q/'qualified/execute_bounded.py').read_bytes();assert plan['pressure_limits']=={'commit_preflight_mib':1792,'commit_running_mib':512,'free_disk_bytes':2147483648,'one_host_one_heavy':True,'owned_job_memory_and_rss_bytes':4294967296,'physical_preflight_mib':2560,'physical_running_mib':1536}
for file in(P/'runtime').rglob('*.rs'):assert file.read_bytes()==(W/'runtime-snapshot'/file.relative_to(P/'runtime')).read_bytes()
assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes();pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
old=(P/'rejected/source.lean').read_text();new=text.replace('\r\n','\n');contracts=lambda s:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',s)];assert contracts(old)==contracts(new)
definitions=lambda s:[m.group(0).strip()for m in re.finditer(r'(?m)^(?:def|structure|inductive) [\s\S]*?(?=^(?:def|structure|inductive|theorem|set_option pp.all)|\Z)',s)]
fixed_old=old.replace('{api with execute := fun child => asCache\n    (executeTransfer backend wordMax capacity pendingKey entryKey dayKey exactMatched ordinary child inputs outputs)}','{api with execute := (fun child => asCache\n    (executeTransfer backend wordMax capacity pendingKey entryKey dayKey exactMatched ordinary child inputs outputs))}')
assert definitions(fixed_old)==definitions(new)
rejected=[json.loads(l)for l in(P/'rejected/events.jsonl').read_text().splitlines()];assert len(rejected)==2 and rejected[-1]['result']['status']=='failed'
pt=read(P/'prior-qualified/plan.json')['targets'][0];pb=(P/'prior-qualified/source.lean').read_bytes();assert sha(pb)==pt['source']['sha256']and len(pb)==pt['source']['bytes'];pr=read(P/'prior-qualified/review.json');pe=[json.loads(l)for l in(P/'prior-qualified/events.jsonl').read_text().splitlines()];assert pe[-1]['result']['status']=='passed';preserved=parse(P/'prior-qualified/complete-23-reports.txt',pt['audit_names'],pe[-1]['result']['audits']);assert len(preserved)==23
current={x['declaration']:x for x in reports};changed_prior=[x['declaration']for x in preserved if current[x['declaration']]!=x]
assert changed_prior==['ShielddSecurity.TransferRawEffectsSource01.'+n for n in ['notes','failed_note_retains_cache_without_semantic_event','successful_note_emits_then_recurses','successful_nullify_emits_all_spends_before_notes']]
prior_source_delta=''.join(difflib.unified_diff(pb.decode().replace('\r\n','\n').splitlines(True),new.splitlines(True)))
matched=0
for r in plan['pins']:
 if r['path']in pins:assert {k:r[k]for k in ['path','bytes','sha256']}==pins[r['path']];matched+=1
out=dict(kind='Independent transported full types/standard axioms/source contracts/exact inherited/runtime/unchanged guard review; no Lean or native execution',manifest_entries=len(M['entries']),plan_pins_matched=matched,fresh_modules=1,fresh_reports=27,full_declarations=reports,inherited_reports=57,custom_imports=owned['selected'],core_floor_exact=True,guard_unchanged=True,preserved_prior_reports=23,prior_reports_counted_again=False,rejected=dict(result=rejected[-1]['result'],compiler_output=(P/'rejected/compiler-output.txt').read_text(),proof_step_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),program_definitions_and_theorem_contracts_unchanged=True),interfaces=R['interfaces'],scope=R['scope'],native_execution='UNRUN',full_transfer='OPEN')
out['rejected']['program_definitions_and_theorem_contracts_unchanged']='Theorem contracts identical; deliveryApi lambda parenthesized to repair parsing, other definitions identical'
out['prior_source_evolution']=dict(changed_declaration_types=changed_prior,exact_source_delta=prior_source_delta,scope='Explicit captured source argument added to note callbacks and reacquired source passed to volume callback; delivery API and three new conclusions added. Earlier source/report set is preserved as predecessor context, not imported or double counted.')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['full_declarations','rejected','custom_imports','interfaces','scope','prior_source_evolution']}))
