from pathlib import Path
import hashlib,json,sys,math,subprocess,re,datetime
P=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-poseidon-call1-plan14');R=P.parent.parent;C=P/'final-two-control-candidate06';F=P/'final-two-result06';D=P/'parent-finaltwo-dispatch06';V=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-poseidon-call1-plan14/parent-final-call14-review01');V.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_bytes());checked={}
def check(e):
 p=Path(e['path']);assert p.is_file() and not p.is_symlink()
 if str(p) not in checked:checked[str(p)]={'sha256':sha(p),'bytes':p.stat().st_size}
 assert checked[str(p)]=={k:e[k] for k in ['sha256','bytes']},str(p)
assert sha(F/'final-result-manifest06.json')=='a1860ff75f5117b55d5366c5aa96e0a1358830df831118fb0469065f35bbb995'
m=load(F/'final-result-manifest06.json');assert len(m['entries'])==185
for e in m['entries'].values():check(e)
for name in ['append-only-envelope06.json','postseal-guard06.json']:
 for value in load(F/name).values():
  if isinstance(value,dict) and set(['path','sha256','bytes'])<=set(value):check(value)
for manifest in [C/'control-candidate-manifest06.json',P/'containment-repair05/candidate05/candidate-manifest05.json',P/'continuation-candidate04/candidate-manifest04.json',P/'containment-failed58-result05/failed58-manifest05.json']:
 for e in load(manifest)['entries'].values():check(e)
sys.path.insert(0,str(C/'maintained'))
from continuation_context import load_context,verify_sources,aggregate_budget,runtime_metadata_size,receipt_name
from admission_gate import Gate
from source_contract import audit_names
from audit_log import validate
si=load(C/'source-inventory06.json');context=load_context(Path(si['continuation_context_file']),si['continuation_context_sha256']);verify_sources(context,si)
receipts=Path(si['execution_paths']['output_dir']);ledger=Path(si['execution_paths']['ledger_directory']);objects=Path(si['execution_paths']['workspace'])/'.lake/build/lib/lean/ShielddSecurity'
g=Gate(ledger,receipts,si['ledger_genesis_sha256'],context)
try:g.acquire();state,events=g.state()
finally:g.release()
assert state['launch_intents']==state['consumed_claims']==len(state['receipts'])==len(state['claims'])==60 and len(events)==state['ledger_events']==180
assert state['ledger_sha256']=='4bd76d6d4e2e9e8d6318cbb0b001fc763409533af6f43b9c529407b621927652'
initial=context['initial_state'];raw=(ledger/'ledger.jsonl').read_bytes();assert hashlib.sha256(b''.join(raw.splitlines(keepends=True)[:174])).hexdigest()==initial['ledger_sha256']
assert all(state[k][n]==h for k in ['receipts','claims'] for n,h in initial[k].items())
expected_records=[];module_reports=[];groups=set()
for ordinal,event in enumerate(events[2::3],1):
 name=event['receipt_name'];rp=receipts/name;row=load(rp);log=rp.with_suffix('.log');assert sha(rp)==state['receipts'][name] and sha(log)==row['log_sha256']
 source=Path(row['command'][-1]);assert sha(source)==row['source_sha256'] and source.stat().st_size==row['source_bytes']
 if row['status']=='failed':
  assert ordinal in [55,56,58] and sha(rp)==context['failed_receipts'][name];continue
 assert row['status']=='passed' and type(row['exit']) is int and row['exit']==0
 obj=objects/(row['module']+'.olean');assert sha(obj)==row['object_sha256'] and obj.stat().st_size==row['object_bytes']>0
 names=audit_names(source,r'^#print axioms (\S+)');checks=audit_names(source,r'^#check @?(\S+)')
 assert names==row['expected_axiom_names'] and checks==row['expected_signature_names']
 data=validate(log.read_text(),names,checks);assert data['full_signature_sha256']==row['full_signature_sha256'] and data['axiom_audits']==row['axiom_audits']==len(names)
 # Existing source auditor reports full signatures and axioms. Cross-check worker's frozen extraction against independently parsed raw.
 for theorem in names:
  worker=next(x for x in load(F/'accepted-RAW398-type-audits06.json')['records'] if x['module']==row['module'] and x['theorem']==theorem)
  assert worker['receipt_sha256']==sha(rp) and worker['log_sha256']==sha(log) and worker['full_type_sha256']==data['full_signature_sha256'][theorem]
  assert hashlib.sha256(worker['full_type'].encode()).hexdigest()==worker['full_type_sha256']
  native_axioms=re.findall(r"'"+re.escape(theorem)+r"' depends on axioms: \[([^\]]*)\]",log.read_text())
  ax=[x.strip() for x in native_axioms[0].split(',')] if native_axioms else []
  assert sorted(worker['axioms'])==sorted(ax)
  expected_records.append(worker)
 groups.add(row['owned_cleanup']['process_group'])
 for key,limit in [('seconds',240),('peak_group_rss_bytes',4*1024**3)]:
  assert type(row[key]) in [int,float] and math.isfinite(row[key]) and 0<=row[key]<=limit
 assert row['minimum_memory_free_percent']>=15 and row['minimum_disk_free_bytes']>=2*1024**3
 assert row['owned_cleanup']['leader_reaped'] is True and type(row['owned_cleanup']['leader_exit_after']) is int and row['owned_cleanup']['leader_exit_after']==0 and row['owned_cleanup']['errors']==[]
 module_reports.append({'ordinal':ordinal,'module':row['module'],'source_sha256':sha(source),'receipt_sha256':sha(rp),'log_sha256':sha(log),'object_sha256':sha(obj),'object_parts':{part.name:sha(part) for suffix in ['.olean.private','.olean.server','.ilean','.ir'] if (part:=obj.with_suffix(suffix)).exists()},'audits':len(names),'seconds':row['seconds']})
assert len(module_reports)==57 and len(expected_records)==398
obs=load(F/'final60-observation06.json');assert obs['state']==state and obs['ALL_attempts']==60 and obs['new59_60_audits']==31
for v in obs['links'].values():
 for key in ['receipt','log','source','current_object']:
  if v.get(key):check(v[key])
 for e in v['current_parts'].values():check(e)
for v in obs['imports_rehashed'].values():
 for key in ['source','object','receipt']:check(v[key])
 for e in v['parts'].values():check(e)
# Verify exact parent acceptance and admission/anchor chain, then controller cleanup.
previous_state=initial;previous_anchor=D/'observations/anchor-0058.json'
for ordinal,module in enumerate(context['future_names'],59):
 ap=D/'admissions'/f'admission-{ordinal:04d}.json';ready=load(D/'admissions'/f'ready-{ordinal:04d}.json');ad=load(ap);assert ready['admission_sha256']==sha(ap) and ad['expected_prior_state']==previous_state
 assert sha(ap)+'.json' in state['claims']
 ins=D/'observations'/f'inspection-{ordinal:04d}.json';iv=load(ins);anchor=D/'observations'/f'anchor-{ordinal:04d}.json';av=load(anchor)
 assert iv['status']=='PARENT_RAW_RESULT_ACCEPTED' and iv['module']==module and iv['audits']==(14 if ordinal==59 else 17)
 assert av['parent_inspection_sha256']==sha(ins) and av['prior_anchor_sha256']==sha(previous_anchor)
 cleanup=load(D/'controller-observations01'/f'cleanup-{ordinal:04d}.json');assert cleanup['leader_reaped'] is True and type(cleanup['runner_exit']) is int and cleanup['runner_exit']==0 and cleanup['errors']==cleanup['remaining_owned_groups']==[]
 groups.update(cleanup['owned_groups']);previous_state=av['state'];previous_anchor=anchor
assert previous_state==state and load(D/'observations/completion.json')['final_state']==state
controller=load(D/'controller-observations01/controller-final01.json');assert controller['status']=='all2-finaltwo-results-observed' and controller['final_state']==state
feeder=load(P/'parent-finaltwo-control-review06/parent-feeder06-typed-exit01.json');assert type(feeder['returncode']) is int and feeder['returncode']==0 and feeder['completion_exists']
ps=subprocess.check_output(['ps','-axo','pid=,pgid=,comm='],text=True);heavy=[x.strip() for x in ps.splitlines() if len(x.split(maxsplit=2))==3 and Path(x.split(maxsplit=2)[2]).name in {'lean','lake','cargo','rustc'}];assert heavy==[]
livegroups={int(x.split(maxsplit=2)[1]) for x in ps.splitlines() if len(x.split(maxsplit=2))==3};assert groups&livegroups==set()
budget=aggregate_budget(context,state,receipts);assert math.isclose(budget['seconds'],362.7732516680699,rel_tol=0,abs_tol=1e-10) and math.isclose(budget['seconds'],obs['ALL_seconds'],rel_tol=0,abs_tol=1e-10)
for r in expected_records:assert 'sorryAx' not in r['full_type'] and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}
(V/'parent-RAW398-type-audits01.json').open('x').write(json.dumps({'classification':'independent raw type/STD extraction only, no new Lean replay','records':expected_records,'audits':398},indent=2)+'\n')
report={'status':'PASS_FINAL60_RAW_SEALS_ACCOUNTING_NO_NEW_REPLAY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(F/'final-result-manifest06.json'),'final_manifest_entries':185,'prior_manifest_entries':[4353,1192,1260,66],'protected_records':5321,'protected_old_object_or_absence':178,'unique_identity_paths_rehashed':len(checked),'final_state':state,'accepted_modules':57,'accepted_audits':398,'new59_60_audits':31,'failures_zero_credit':[55,56,58],'original60_remaining':0,'budget':budget,'metadata_bytes':runtime_metadata_size(context),'module_reports':module_reports,'RAW398_type_audits_sha256':sha(V/'parent-RAW398-type-audits01.json'),'parent_admission_anchor_chain_verified':True,'controller_owned_groups_absent':True,'heavy':heavy,'parent_new_Lean_runs':0,'source_object_import_bytes_verified':True,'full_Transfer':'OPEN'}
out=V/'parent-final-RAW-inspection01.json';out.open('x').write(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['final_state','module_reports']}))

