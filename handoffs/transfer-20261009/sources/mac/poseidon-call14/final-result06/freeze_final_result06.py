"""Read-only additive final actual result seal; no verifier or dispatch. Raw logs and cache identities stay local."""
from pathlib import Path
import hashlib,json,math,re,subprocess,sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
Q=Path(__file__).resolve().parent;R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');P=R/'work/mac-poseidon-call1-plan14';C=P/'final-two-control-candidate06';D=P/'parent-finaltwo-dispatch06';V=P/'parent-finaltwo-control-review06';receipts=R/'outputs/mac-poseidon-call1-plan14/probes01';L=R/'outputs/mac-poseidon-call1-plan14/overall-ledger01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_bytes())
def ident(p):return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def save(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
sys.path.insert(0,str(C/'maintained'))
from continuation_context import load_context,verify_sources,aggregate_budget,validate_history
from audit_log import validate
si=load(C/'source-inventory06.json');ctx=load_context(Path(si['continuation_context_file']),si['continuation_context_sha256']);verify_sources(ctx,si)
for manifest in [C/'control-candidate-manifest06.json',P/'containment-repair05/candidate05/candidate-manifest05.json',P/'continuation-candidate04/candidate-manifest04.json']:
 for e in load(manifest)['entries'].values():assert ident(Path(e['path']))==e
raw=(L/'ledger.jsonl').read_bytes();events=[];previous='0'*64;claims={};intents={};final={}
for line in raw.splitlines(keepends=True):
 e=json.loads(line);assert (json.dumps(e,sort_keys=True,separators=(',',':'))+'\n').encode()==line and e['sequence']==len(events)+1 and e['previous_event_sha256']==previous
 previous=hashlib.sha256(line).hexdigest();events.append(e)
 if e['kind']=='claim_consumed':assert e['claim']['name'] not in claims;claims[e['claim']['name']]=e['claim']['sha256']
 elif e['kind']=='launch_intent':assert e['receipt_name'] not in intents;intents[e['receipt_name']]=e
 elif e['kind']=='final':assert e['receipt_name'] in intents and e['receipt_name'] not in final;final[e['receipt_name']]=e['receipt_sha256']
 else:raise AssertionError('unknown kind')
assert len(events)==180 and len(claims)==len(intents)==len(final)==60
assert hashlib.sha256(b''.join(raw.splitlines(keepends=True)[:174])).hexdigest()==ctx['initial_state']['ledger_sha256']
assert {p.name:sha(p) for p in (L/'claims').iterdir()}==claims and {p.name:sha(p) for p in receipts.glob('build-*.json')}==final
links={};audit_total=0;passed=0;seconds=0;structured=[];import_links={};parts_suffixes=['.olean.private','.olean.server','.ilean','.ir']
objects=Path(si['execution_paths']['workspace'])/'.lake/build/lib/lean/ShielddSecurity'
failed_slots={'build-TransferPoseidonCall14Program01-01.json','build-TransferPoseidonCall14Program01-02.json','build-TransferPoseidonCall14Proof01-01.json'}
for name,digest in final.items():
 p=receipts/name;d=load(p);assert sha(p)==digest;log=p.with_suffix('.log');assert sha(log)==d['log_sha256'];src=Path(d['command'][-1]);assert sha(src)==d['source_sha256'];obj=Path(d['command'][d['command'].index('-o')+1]);observed=ident(obj) if obj.exists() else None
 if d['command_started']:assert type(d['seconds']) in [int,float] and math.isfinite(d['seconds']);seconds+=d['seconds']
 if d['status']=='passed':
  assert type(d['exit']) is int and d['exit']==0 and observed['sha256']==d['object_sha256']
  text=log.read_text();parsed=validate(text,d['expected_axiom_names'],d['expected_signature_names']);assert parsed['full_signature_sha256']==d['full_signature_sha256'] and parsed['axiom_audits']==d['axiom_audits'];audit_total+=parsed['axiom_audits'];passed+=1
  for theorem,digest in parsed['full_signature_sha256'].items():
   full=re.findall(r'^@?'+re.escape(theorem)+r'\s*:[\s\S]*?(?=^\''+re.escape(theorem)+r'\')',text,re.M);assert len(full)==1 and hashlib.sha256(full[0].strip().encode()).hexdigest()==digest
   axiom_match=re.findall(r"^'"+re.escape(theorem)+r"' (?:depends on axioms: \[([^]]*)\]|(does not depend on any axioms))",text,re.M);assert len(axiom_match)==1
   structured.append({'axioms':[a.strip() for a in axiom_match[0][0].split(',') if a.strip()], 'module':d['module'],'theorem':theorem,'full_type':full[0].strip(),'full_type_sha256':digest,'receipt_sha256':sha(p),'log_sha256':sha(log),'classification':'accepted actual named audit; scope remains its exact printed type'})
 else:
  assert name in failed_slots and d['status']=='failed' and d['fresh_credit']==0 and type(d['exit']) is int and d['exit']==1
  # Current Proof object belongs solely to passed59, never to failed58.
 parts={part.name:ident(part) for suffix in parts_suffixes if (part:=obj.with_suffix(suffix)).exists()}
 links[name]={'receipt':ident(p),'log':ident(log),'source':ident(src),'current_object':observed,'current_parts':parts,'object_produced_by_this_attempt':d['status']=='passed','failed_historical_object_observation':('Program current object belongs solely to passed57, not failed55/56' if d['module'].endswith('Program01') else 'Proof current object belongs solely to passed59, not failed58') if name in failed_slots else None,'status':d['status'],'seconds':d['seconds'],'audits':d.get('axiom_audits',0) if d['status']=='passed' else 0,'exit':d['exit'],'command':d['command'],'resources':{k:d.get(k) for k in ['peak_group_rss_bytes','minimum_memory_free_percent','minimum_disk_free_bytes','owned_cleanup']}}
 for n,e in d.get('frozen_imports',{}).items():
  if n in ['package','official_import_closure']:continue
  parent=R/e['receipt_path'];r=load(parent);assert sha(parent)==e['receipt_sha256'] and r['status']=='passed' and r['source_sha256']==e['source_sha256'] and r['object_sha256']==e['object_sha256']
  isrc=Path(r['command'][-1]);iobj=objects/(n+'.olean');assert sha(isrc)==e['source_sha256'] and sha(iobj)==e['object_sha256']
  assert {part.name:sha(part) for suffix in parts_suffixes if (part:=iobj.with_suffix(suffix)).exists()}==e['parts']
  import_links[sha(p)+':'+n]={'source':ident(isrc),'object':ident(iobj),'receipt':ident(parent),'parts':e['parts']}
assert passed==57 and audit_total==len(structured)==398 and math.isclose(seconds,343.6519449180778+10.420361166994553+8.70094558299752,abs_tol=1e-9)
state={'ledger_sha256':sha(L/'ledger.jsonl'),'ledger_events':180,'launch_intents':60,'consumed_claims':60,'receipts':final,'claims':claims,'genesis_sha256':sha(L/'genesis01.json')}
assert all(state['receipts'][n]==h for n,h in ctx['initial_state']['receipts'].items()) and all(state['claims'][n]==h for n,h in ctx['initial_state']['claims'].items())
validate_history(ctx,state,events,receipts,L,ctx['original_names'])
assert all((objects/(n+'.olean')).is_file() for n in si['successor_topological_order'])
assert not (D/'admissions/ready-0061.json').exists() and not (D/'admissions/admission-0061.json').exists()
cleanups={}
for ordinal in [59,60]:
 p=D/'controller-observations01'/f'cleanup-{ordinal:04d}.json';d=load(p);assert d['leader_reaped'] and not d['errors'] and not d['remaining_owned_groups'];cleanups[str(ordinal)]=ident(p)
heavy=[line for line in subprocess.check_output(['ps','-axo','pid=,comm='],text=True,timeout=10).splitlines() if Path(line.split(maxsplit=1)[1]).name in {'lake','lean','cargo','rustc'}];assert not heavy
(Q/'ledger-final60.jsonl').write_bytes(raw);(Q/'claims').mkdir()
for p in (L/'claims').iterdir():(Q/'claims'/p.name).write_bytes(p.read_bytes())
(Q/'raw-local-only').mkdir()
for n in final:
 for p in [receipts/n,(receipts/n).with_suffix('.log')]:(Q/'raw-local-only'/p.name).write_bytes(p.read_bytes())
save(Q/'accepted-RAW398-type-audits06.json',{'classification':'existing actual log extraction only; ZERO new kernel replay','records':structured,'audits':398})
budget=aggregate_budget(ctx,state,receipts)
metadata=__import__('continuation_context').runtime_metadata_size(ctx)
assert budget['attempts']==60 and metadata<=16*1024**2
config=load(V/'config-dispatch06.json'); invocation=load(V/'controller-launch-invocation06.json')
control_scope={'count':13,'r00_syntax_guards':6,'representative_tail_row_renaming_guards':4,'fixed_metadata_guards':3,'semantic_inequality_claim':False,'whole_candidate_checker':False}
report={'classification':'actual final-two execution, local conditional Call14 endpoint; no full Transfer certification','state':state,'ALL_attempts':60,'ALL_seconds':seconds,'accepted_modules':57,'existing_accepted_audits':398,'new59_60_audits':31,'failed_ordinals':[55,56,58],'failed_entire_module_credit':0,'attempts_remaining_original60':0,'seconds_remaining_original1200':1200-seconds,'links':links,'imports_rehashed':import_links,'controller_final':ident(D/'controller-observations01/controller-final01.json'),'controller_cleanup':cleanups,'controller_invocation':ident(V/'controller-launch-invocation06.json'),'exact_command':invocation['command'],'external_approval':ident(V/'context-approved01.json'),'approved_config':ident(V/'config-dispatch06.json'),'parent_dispatch_files':{str(p):ident(p) for sub in ['admissions','observations'] for p in (D/sub).glob('*.json')},'ordinal61_unmapped':True,'candidate4353_ancestor1192_1260_unchanged':True,'fixed5321_old_objects178_unchanged':True,'fixed174_prefix_claims_receipts_unchanged':True,'charged_budget':budget,'runtime_metadata_bytes':metadata,'heavy_processes':heavy,'automatic_retry':False,'local_scope':{'selected_rows':837,'materialized_steps':627,'one_copy_step':1,'total_steps':628,'domain':24,'arity':6,'original_inputs':[20,21,27,28,29,30],'original_columns':[23,24,30,31,32,33],'semantic_scope':'same final assignment, independent two-block width6 hash; exact printed types authoritative','copy_and_field_premises':'explicit base0=1, base copy linkage, Field/CharP and 4!=0 as printed','input_carry':'all six block0 outputs carried; block1 adds original input33 only; no IV reset','capture_binding':'qualified data associations and component selected rows; no full parent positional rowAt theorem','controls':control_scope},'OPEN':['child join','native callsite/consumer identity','whole candidate checker','full parent rowAt','full captured relation','Full Transfer','Hasse','cardinality']}
save(Q/'final60-observation06.json',report)
save(Q/'publication-scope06.json',{'exclude_from_repository':['raw-local-only logs','objects','object companions','caches','composed workspace'],'actual_accepted_type_records':398,'failed_ordinals_zero_credit':[55,56,58],'scope':report['local_scope'],'OPEN':report['OPEN']})
entries={str(p.relative_to(Q)):ident(p) for p in sorted(Q.rglob('*')) if p.is_file()};manifest=Q/'final-result-manifest06.json';save(manifest,{'classification':'immutable actual final result producer; raw observations local only','entries':entries,'protected_manifests':[ident(p) for p in [C/'control-candidate-manifest06.json',P/'containment-repair05/candidate05/candidate-manifest05.json',P/'continuation-candidate04/candidate-manifest04.json']],'actual_attempts':60,'actual_seconds':seconds,'accepted_modules':57,'actual_audits':398,'failed_credit':0})
for e in entries.values():assert ident(Path(e['path']))==e
save(Q/'append-only-envelope06.json',{'classification':'append-only result envelope; all historical entries remain immutable','producer':ident(manifest),'observation':ident(Q/'final60-observation06.json'),'final_ledger':ident(L/'ledger.jsonl'),'parent_final_anchor':ident(D/'observations/anchor-0060.json'),'all_sealed_prior_paths_unchanged':True})
save(Q/'postseal-guard06.json',{'status':'PASS identity-only; no kernel replay','producer':ident(manifest),'envelope':ident(Q/'append-only-envelope06.json'),'entries':len(entries),'actual_ledger_sha256':sha(L/'ledger.jsonl'),'protected5321':len(ctx['fixed_records']),'heavy':heavy})
print(json.dumps({'manifest':ident(manifest),'envelope':ident(Q/'append-only-envelope06.json'),'guard':ident(Q/'postseal-guard06.json'),'observation':ident(Q/'final60-observation06.json'),'attempts':60,'seconds':seconds,'accepted':57,'audits':398,'heavy':heavy},indent=2))
