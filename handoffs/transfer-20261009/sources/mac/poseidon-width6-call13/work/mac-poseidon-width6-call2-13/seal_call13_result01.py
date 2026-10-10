"""Freeze actual finite Call13 result and full named audits; no further Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width6-call2-13';K=O/'kernel-successors01';T=S/'successor-source05';F=S/'final-result01';assert not F.exists();F.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
identity=lambda p:{'sha256':sha(p),'bytes':p.stat().st_size}
def write(p,v):
    with p.open('x') as h:json.dump(v,h,indent=2);h.write('\n')
source_inventory=json.loads((T/'source-inventory01.json').read_text());names=set(source_inventory['modules'])
M=T/'maintained';inventory=json.loads((T/'maintained-inventory01.json').read_text());assert {p.name for p in M.iterdir()}==set(inventory['maintained_files'])
for name,e in inventory['maintained_files'].items():assert identity(M/name)==e
sys.path.insert(0,str(M));from audit_log import validate
all_attempts={p:json.loads(p.read_text()) for p in K.glob('build-*.json')}
assert len(all_attempts)==45
selected={r['module']:(p,r) for p,r in all_attempts.items() if r['status']=='passed'};assert len(selected)==43
for name,e in source_inventory['accepted_probes'].items():
    p=R/e['receipt_path'];r=json.loads(p.read_text());assert sha(p)==e['receipt_sha256'];selected[name]=(p,r)
assert set(selected)==names and len(selected)==45
failure={p:r for p,r in all_attempts.items() if r['status']!='passed'};assert len(failure)==2 and all(r['fresh_credit']==0 and r['exit']==1 for r in failure.values())
audits=[];census={}
for name,(p,r) in selected.items():
    log=p.with_suffix('.log');source=T/'generated01'/(name+'.lean');project=T/'project/ShielddSecurity'/(name+'.lean');obj=T/'project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
    assert r['status']=='passed' and sha(log)==r['log_sha256'] and identity(source)==source_inventory['modules'][name] and sha(source)==sha(project)==r['source_sha256'] and sha(obj)==r['object_sha256']
    text=log.read_text();v=validate(text,r['expected_axiom_names'],r['expected_signature_names']);assert v['axiom_audits']==r['axiom_audits'] and v['full_signature_sha256']==r['full_signature_sha256']
    for theorem,digest in r['full_signature_sha256'].items():
        signature=re.findall(r'^@?'+re.escape(theorem)+r'\s*:[\s\S]*?(?=^\''+re.escape(theorem)+r'\')',text,re.M)[0].strip();assert hashlib.sha256(signature.encode()).hexdigest()==digest
        ax=re.findall(r"'"+re.escape(theorem)+r"' depends on axioms: \[([^]]*)\]",text)
        axioms=[a.strip() for a in ax[0].split(',')] if ax else [];assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
        audits.append({'module':name,'theorem':theorem,'full_type':signature,'full_type_sha256':digest,'axioms':axioms,'receipt_path':str(p.relative_to(R)),'receipt_sha256':sha(p),'log_sha256':sha(log)})
    census[name]={'classification':'actual fresh bounded execution, NOT inherited cache replay','receipt_path':str(p.relative_to(R)),**identity(p),
                 'source_sha256':r['source_sha256'],'source_bytes':r['source_bytes'],'object_sha256':r['object_sha256'],'main_object_bytes':r['object_bytes'],
                 'actual_command':r['command'],'seconds':r['seconds'],'peak_group_RSS_bytes':r['peak_group_rss_bytes'],'audits':r['axiom_audits'],
                 'maintained_guard_sources_sha256':r.get('guard_sources_sha256'),'cost_only_True_marker':False}
assert len(audits)==247 and len({a['theorem'] for a in audits})==247
write(F/'full-audits01.json',{'status':'passed','fresh_successful_modules':45,'exact_full_type_and_standard_axiom_records':audits,'audits':247,
 'counts_distinct':'full types247 and axiom audits247; every full_type hash matches actual immutable successful receipt; failed recovery output excluded'})
root=selected['TransferPoseidonCall13Proof01'][1];owned={n:e for n,e in root['frozen_imports'].items() if n not in {'package','official_import_closure'}}
new_root=(set(owned)&names)|{'TransferPoseidonCall13Proof01'};inherited=set(owned)-names;assert len(new_root)==43 and len(inherited)==98
root_audits=sum(census[n]['audits'] for n in new_root);assert root_audits==230
write(F/'source-object-receipt-census01.json',{'schema':'call13-actual45-module-census01','modules':census,'ALLfresh_modules':45,'ALLfresh_audits':247,
 'root_fresh_modules':43,'root_fresh_audits':230,'root_inherited_owned_modules':98,'root_owned_module_closure_including_self':141,
 'nonroot_fresh_modules':{'TransferPoseidonCall13Checked01':4,'TransferPoseidonCall13Controls01':13},'root_imports':root['frozen_imports'],
 'inherited_credit':'98 inherited modules ZERO fresh execution; exact original source/object/receipt ancestry in root frozen_imports/probe-imports01',
 'probes':'two actual earlier Call13 admitted executions included, NOT copied receipts from older campaign stages'})
wall=sum(r.get('seconds',0) for r in all_attempts.values())+sum(selected[n][1]['seconds'] for n in source_inventory['accepted_probes'])
all_resources=[r for r in all_attempts.values()]+[selected[n][1] for n in source_inventory['accepted_probes']]
objdir=T/'project/.lake/build/lib/lean/ShielddSecurity';object_bytes=sum(p.stat().st_size for name in names for p in objdir.glob(name+'.*') if p.is_file())
failed=[]
for p,r in failure.items():failed.append({'module':r['module'],'receipt_path':str(p.relative_to(R)),**identity(p),'source_sha256':r['source_sha256'],'log_path':str(p.with_suffix('.log').relative_to(R)),'log_sha256':sha(p.with_suffix('.log')),'exit':r['exit'],'seconds':r['seconds'],'peak_RSS_bytes':r['peak_group_rss_bytes'],'proof_credit':0,
 'disposition':'Program01-01 implicit Field inference' if p.name.endswith('-01.json') else 'Program01-02 incorrect left-associated append case split; failed-elaboration recovery output ZERO proof credit'})
processes=subprocess.check_output(['ps','-axo','pid=,comm='],text=True);heavy=[x.strip() for x in processes.splitlines() if Path(x.split(maxsplit=1)[1]).name in {'lean','lake','cargo','rustc'}];assert not heavy
scope={'schema':'call13-precise-scope01','mathematical_endpoint':'SAME final assignment; generic Field F of explicit characteristic Shared01.p, base0=1, basecopy=base0, explicit(4:F)!=0',
 'hash':'Poseidon.hash6 pinned width6parameters, domain36, five inputs [base34,base35,base36,base42,base43], IV1316/arity5 absorption',
 'construction':'313steps=312materialized+ONEtautologicalcopy step;417selectedrows=416arithmetic+ONE actual copy row; originalRows all satisfied',
 'fresh_writes':'[24308,24724); all22735 original source input columns3+i preserved; copy200692 and all columns outside fresh window preserved',
 'prior_rows':'ONLY conditional prior list supplied already satisfied and whose every actual term support avoids fresh write window; no claim whole prior capture preserved',
 'row_association':'captureIndices equality range1570..1985 plus200769 is FORMAL index-list partition. Exact original RowSpool/DB bodies/provenance qualified DATA. No formal full parent rowAt/whole200770 relation inclusion theorem',
 'result':'internal final state[1] LC mathematical hash result. raw21951-to-child-inputLC exact DATA association, not native callsite/runtime consumer identity theorem',
 'checker':'R00 mutable LOCAL production guard; fixed overall endpoint metadata restatement, NOT a whole-call mutable candidate guard',
 'controls':{'R00_local_production_guard_refusals':6,'representative_tail_chunk00_row_identity_refusals':4,'fixed_endpoint_metadata_refusals':3,'total':13,
 'limits':['R00 controls ONLY first round, not all65candidate guards','missing_local_copy removes R00 local copy only, not a theorem rejecting omission of joined sharedcopy',
 'tail omission guard/representative row checks only; wrong offset1251 remains injective, no injectivity/frame rejection claim','metadata wrongdomain/arity/inputorder checks fixed metadata only',
 'checker=false theorems, NOT mutated semantic inequalities']},
 'root_counts':{'fresh_modules':43,'audits':230,'inherited':98,'owned_closure':141},'ALLstage_counts':{'fresh_passes':45,'audits':247,'failed_attempts':2,'ALLattempts':47},
 'OPEN':['whole mutable candidate checker coverage','childhash3join/call1','full parent rowAt/global200770relation','native/callsite/rawconsumer identity','laterconsumer/upstreamsemantic/native stateclosure','full Transfer certification'],
 'publication':'await parent actual Opus5.5 review and existing-log re-audit; no pushes/atomic evidence certification refresh performed'}
write(F/'scope01.json',scope)
write(F/'result01.json',{'status':'finite kernel endpoints passed; awaiting independent review/publication','ALLfresh_modules':45,'ALLexact_full_types':247,'ALLstandard_axiom_audits':247,
 'root_fresh_modules':43,'root_audits':230,'root_inherited':98,'root_owned_closure':141,'actual_step_count':313,'actual_selected_row_count':417,'actual_rejection_controls':13,
 'ALLattempts':47,'failed_attempts':failed,'ALLLean_wall_seconds':wall,'remaining_attempt_budget':13,'remaining_Lean_wall_budget_seconds':1200-wall,
 'maximum_sampled_RSS_bytes':max(r.get('peak_group_rss_bytes',0) for r in all_resources),'maximum_module_Lean_seconds':max(r['seconds'] for r in all_resources),
 'minimum_memory_free_percent':min(r.get('minimum_memory_free_percent',100) for r in all_resources),'minimum_disk_free_bytes':min(r.get('minimum_disk_free_bytes',2**63) for r in all_resources),
 'generated_source_bytes':875550,'owned45_current_object_part_bytes':object_bytes,'source_plus_objects_bytes':875550+object_bytes,
 'portable_replay_sources':45,'portable_replay_bytes':875550,'portable_DATA_only':True,'accepted_module_replays':0,'heavy_processes':heavy,'fullTransfer':'OPEN'})
# Verify every previously sealed path, without changing or silently refreshing a manifest.
prior={}
for p in [O/'plan-manifest01.json',O/'probe-manifest01.json',O/'successor-plan-manifest01.json',S/'successor-source03/source-readiness-manifest01.json',S/'successor-source04/repair-source-manifest01.json',S/'successor-source05/repair-source-manifest01.json']:
    d=json.loads(p.read_text())
    for relative,e in d['entries'].items():assert identity(R/relative)=={k:e[k] for k in ['sha256','bytes']}
    prior[str(p.relative_to(R))]=identity(p)
write(F/'prior-seal-bindings01.json',{'status':'passed','manifests':prior,'all_prior_entry_paths_bytes_UNCHANGED':True,'all_kernel_attempt_receipts':{str(p.relative_to(R)):identity(p) for p in all_attempts},'no_unchanged_kernel_replays':True})
readme=F/'RESULT.md'
with readme.open('x') as h:h.write('''Finite Call13 kernel stage completed:45 fresh modules,247 exact full-type and standard-axiom audits. Root closure43fresh/230audits+98inherited=141owned; Checked4 and Controls13 audits counted separately.47attempts includes TWO failed Program elaborations with ZERO proof credit. No accepted module rerun.

The root proves the SAME final assignment satisfies417selectedrows after313steps (one shared copy) and its finalstate[1] equals independent width6hash domain36 on five original input columns34/35/36/42/43. Preconditions are generic Field of pinned characteristic, base0=1, basecopy=base0, and explicit4!=0. All22735original inputs, copy and outside-write columns are preserved. Prior rows have a support-conditioned frame only.

13 actual controls are6R00LOCAL production refusals,4representative tail chunk row identity refusals,3fixed metadata refusals; no mutated semantic inequality or whole candidate guard claim. Exact raw/DB/RowSpool association is qualified DATA; captureIndices partition is a formal list equality, not full parent rowAt. raw21951/child association, childjoin/call1/native/global/fullTransfer remain OPEN.

Closed14file maintained recipe in successor-source05 regenerates all45source bytes under-I-B-S, no Lean. Old plan/probe/source03/source04/source05 seals, original counter directory and failed source/receipts remain unchanged. Parent actual Opus/re-audit/publication remains required. Heavy lane quiescent; no Git writes.
''')
entries={}
def add(p,c):
    assert p.is_file() and not p.is_symlink();entries[str(p.relative_to(R))]={**identity(p),'classification':c}
for p in M.iterdir():add(p,'maintained generator/template/runner/portable helper')
for p in (T/'generated01').iterdir():add(p,'accepted generated source')
for p,r in all_attempts.items():add(p,'actual successful receipt' if r['status']=='passed' else 'failed elaboration receipt ZERO proof credit')
for name,(p,r) in selected.items():
    if name in source_inventory['accepted_probes']:add(p,'actual earlier Call13 probe receipt, no rerun')
for p in K.glob('official-imports-*.json'):add(p,'deduplicated official import identity manifest')
for p in [T/'maintained-inventory01.json',T/'source-inventory01.json',T/'generation01/successor-generation01.json',T/'probe-generation01/probe-generation01.json',T/'replay01/replay-result01.json',T/'readiness-controls01.json',T/'cleanup-controls01.json',O/'compact-input02.json',O/'successor-topology01.json',O/'probe-imports01.json',O/'probe-full-audits01.json',O/'qualification-result01.json',O/'selection-guard01.json',O/'compact-projection-check01.json',R/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381-wide.json',Path(__file__)]:add(p,'data/qualification/recipe/provenance')
for p in [S/'successor-source01/generated01/TransferPoseidonCall13Program01.lean',S/'successor-source04/generated01/TransferPoseidonCall13Program01.lean']:add(p,'immutable failed generated source ZERO proof credit')
for p in F.iterdir():add(p,'result/scope/actual full audit/source-object-receipt census')
manifest=F/'producer-manifest01.json'
write(manifest,{'schema':'call13-finite-result-producer01','entries':entries,'prior_seals':prior,'module_census':{'ALLfresh45_audits247':True,'root43_audits230_inherited98':True},
 'preserved_failure_logs_LOCAL_only':{str(p.with_suffix('.log').relative_to(R)):identity(p.with_suffix('.log')) for p in failure},
 'publication_inventory':'compact1.6MB generation input, exact generated/maintained bytes, receipts, one deduplicated official manifest, data/provenance/results; NO raw captures/full10.58MB descriptor/cache/composedworkspace/log files',
 'status':'await independent actual Opus5.5/parent acceptance, fullTransferOPEN'})
for relative,e in entries.items():assert identity(R/relative)=={k:e[k] for k in ['sha256','bytes']}
guard=F/'post-seal-guard01.json';write(guard,{'status':'passed','producer_manifest_sha256':sha(manifest),'entries':len(entries),'actual_full_type_hashes':247,'kernel_runs_after_finish':0,'all_prior_sealed_paths_unchanged':True,'heavy_processes':heavy})
envelope=F/'post-seal-envelope01.json';write(envelope,{'schema':'call13-finite-result-envelope01','entries':{str(p.relative_to(R)):identity(p) for p in [manifest,guard]},'fullTransfer':'OPEN','publication_requires_parent_review':True})
print(json.dumps({'producer_manifest_sha256':sha(manifest),'entries':len(entries),'envelope_sha256':sha(envelope),'guard_sha256':sha(guard),'full_audits_sha256':sha(F/'full-audits01.json'),'scope_sha256':sha(F/'scope01.json'),'result_sha256':sha(F/'result01.json'),'ALLwall_seconds':wall,'object_bytes':object_bytes,'heavy_processes':heavy}))
