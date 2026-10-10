"""Derive a portable identity/accounting excerpt from immutable actual results."""
from pathlib import Path
import json,hashlib
P=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-poseidon-call1-plan14');F=P/'final-two-result06';V=P/'parent-final-call14-review01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_bytes())
manifest=load(F/'final-result-manifest06.json');assert sha(F/'final-result-manifest06.json')=='a1860ff75f5117b55d5366c5aa96e0a1358830df831118fb0469065f35bbb995'
obs=load(F/'final60-observation06.json');actual=[];bindings={}
for key,e in manifest['entries'].items():
 if not key.startswith('raw-local-only/') or not key.endswith('.json'):continue
 p=Path(e['path']);assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'];r=load(p)
 fields=['module','status','command_started','fresh_credit','expected_ordinal','runner_sha256','source_inventory_sha256','maintained_inventory_sha256','admission_sha256','timeout_seconds','process_group_rss_limit_bytes','lean_heap_limit_MiB','finite_option_guard','source_sha256','source_bytes','command','environment','expected_axiom_names','expected_signature_names','owned_process_group','owned_cleanup','exit','seconds','peak_group_rss_bytes','minimum_memory_free_percent','minimum_disk_free_bytes','log_sha256','axiom_audits','full_signature_sha256','object_sha256','object_bytes','charged_source_object_bytes']
 row={k:r[k] for k in fields if k in r};row['actual_receipt_identity']={'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size};row['local_raw_stdout_policy']='Retained local only; original log hash copied without inventing a portable raw transcript.'
 actual.append(row)
 for imp,v in r.get('frozen_imports',{}).items():
  h=hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest();bindings.setdefault(h,{'import':imp,'original_record':v})
actual.sort(key=lambda r:r['expected_ordinal']);assert [r['expected_ordinal'] for r in actual]==list(range(1,61))
passed=[r for r in actual if r['status']=='passed'];assert len(passed)==57 and sum(r['axiom_audits'] for r in passed)==398
assert [r['expected_ordinal'] for r in actual if r['status']!='passed']==[55,56,58]
fields=['ALL_attempts','ALL_seconds','accepted_modules','existing_accepted_audits','new59_60_audits','failed_ordinals','failed_entire_module_credit','attempts_remaining_original60','charged_budget','runtime_metadata_bytes','heavy_processes','automatic_retry','local_scope','OPEN','ordinal61_unmapped']
report={'schema':'portable-call14-actual-result-identity-excerpt-v1','classification':'Derived retained actual receipt and accounting fields, no new kernel/review/certification credit','producer_manifest_sha256':sha(F/'final-result-manifest06.json'),'original_observation_identity':{'path':str(F/'final60-observation06.json'),'bytes':(F/'final60-observation06.json').stat().st_size,'sha256':sha(F/'final60-observation06.json')},'observed_fields':{k:obs[k] for k in fields},'actual_receipts':actual,'qualified_import_records_deduplicated_by_exact_JSON_identity':bindings,'full_actual_import_receipt_occurrences_remain_local':True,'parent_independent_inspection_identity':{'path':str(V/'parent-final-RAW-inspection01.json'),'sha256':sha(V/'parent-final-RAW-inspection01.json')},'parent_actual_type_audits_identity':{'path':str(V/'parent-RAW398-type-audits01.json'),'sha256':sha(V/'parent-RAW398-type-audits01.json')},'all_original_receipts_unchanged':True,'new_Lean_runs':0,'final_certification_refresh':False,'full_Transfer':'OPEN'}
(V/'portable-actual-result01.json').open('x').write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'receipts':60,'passed':57,'audits':398,'import_records':len(bindings),'portable_bytes':(V/'portable-actual-result01.json').stat().st_size,'sha256':sha(V/'portable-actual-result01.json')}))

