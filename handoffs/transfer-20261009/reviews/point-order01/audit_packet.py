"""Rehash transported sources, reconstruct wrappers and parse existing audits."""
import datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];F=HERE/'frozen';REPO=ROOT/'work/shared-build-handoff';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((F/'manifest.json').read_text());r=json.loads((F/'receipt.json').read_text());d=json.loads((F/'dependency-resolution.json').read_text())
assert sha(F/'manifest.json')=='c0b62cc21c8f1faa70208009d11aae9f8f70429703232efa0cad556ec0c27678'
for n,x in m['files'].items():assert sha(F/n)==x['sha256'] and (F/n).stat().st_size==x['bytes']
assert r['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a' and r['mathlib_sha']=='c5ea00351c28e24afc9f0f84379aa41082b1188f' and r['lean_version']=='4.30.0'
assert r['actual_freeze_checkout_head']=='7ea375d0f6e6f9eb5b3ddcb24341e60fcd734cef'
depcounts={'canonical':0,'packet_new':0}
for x in d:
    if x['reference_disposition']=='tracked at freeze HEAD':
        assert sha(REPO/x['repository_reference'])==x['original_source_sha256']
        carried=F/'canonical-dependencies'/(x['name']+'.lean')
        if carried.exists():assert sha(carried)==x['original_source_sha256']
        depcounts['canonical']+=1
    else:assert sha(HERE/'resolved-source'/(x['name']+'.lean'))==x['original_source_sha256'];depcounts['packet_new']+=1
batch_inputs={}
for batch,b in r['batches'].items():
    p=F/'inputs'/batch;inputs=json.loads((p/'manifest.json').read_text());batch_inputs[batch]=inputs
    assert sha(p/'manifest.json')==b['source_manifest_sha256'] and b['actual_exit']==0
    recipe=b['recipe'];assert recipe['threads']==1 and recipe['memory_MiB']==1536 and recipe['finite_seconds_per_module']==240
    assert json.loads((p/'recipe.json').read_text())==recipe
    assert sha(F/'recipes'/('root-'+batch+'.ps1'))==recipe['guard_sha256'].lower()
    assert sha(F/'recipes'/('audit-'+batch+'.py'))==recipe['audit_sha256'].lower()
    admission=json.loads((F/'boundary/point-order/admission.json').read_text());assert admission['heavy_processes']==[] and admission['guard_sha256'].lower()==recipe['guard_sha256'].lower()
    assert admission['memory']['PhysicalKiB']>=3145728 and admission['memory']['CommitFreeKiB']>=2621440
    guard=(F/'recipes'/('root-'+batch+'.ps1')).read_text()
    assert "$env:LEAN_NUM_THREADS='1'" in guard and "'-j1','-M','1536'" in guard and 'finite-240s-budget' in guard and 'host-memory-pressure' in guard
accepted=[];names_all=[]
for name,leaf in r['modules'].items():
    inputs=batch_inputs[leaf['batch']];names=inputs['expected_theorems_by_module'][name];source=HERE/'resolved-source'/(name+'.lean');candidate=F/'audited-source'/(name+'.lean')
    assert sha(source)==inputs['sources'][name]['sha256'];body=re.sub(r'(?m)^(?:set_option pp\.all true in\r?\n)?#(?:check|print axioms)[^\r\n]*\r?\n', '', source.read_text(encoding='utf-8-sig'));end=list(re.finditer(r'(?m)^end\s+([\w.]+)\s*$',body))[-1].start()
    checks=''.join(f'\nset_option pp.all true in\n#check @{n}\n#print axioms {n}\n' for n in names)
    assert (body[:end]+checks+body[end:]).encode()==candidate.read_bytes(),name
    assert sha(candidate)==inputs['audited_candidates'][name]
    audit=leaf['audit'];assert audit==json.loads((F/'audits'/(name+'.json')).read_text());assert audit['original_source_sha256']==sha(source) and audit['candidate_sha256']==sha(candidate)
    assert leaf['actual_exit']==0 and audit['full_types_checked'] and audit['audits']==len(names)==len(audit['axioms'])
    stdout=F/'review-audit-text'/(name+'.txt');assert sha(stdout)==leaf['stdout_sha256'];text=stdout.read_text();assert 'error:' not in text and 'sorryAx' not in text
    observed=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
    assert sorted(n for n,_ in observed)==sorted(audit['axioms'])
    signatures={}
    for n,v in observed:
        axioms=[x.strip() for x in v.split(',') if x.strip()];assert set(axioms)<={'propext','Classical.choice','Quot.sound'} and sorted(axioms)==sorted(audit['axioms'][n])
        hits=re.findall(r'^@?'+re.escape(n)+r'(?:\.\{[^}]*\})?\s*:[\s\S]*?(?=^\''+re.escape(n)+r'\')',text,re.M);assert len(hits)==1,n
        signatures[n]=hashlib.sha256(hits[0].strip().encode()).hexdigest();names_all.append(n)
    seconds=(datetime.datetime.fromisoformat(leaf['end'])-datetime.datetime.fromisoformat(leaf['start'])).total_seconds();assert 0<seconds<=240
    accepted.append({'module':name,'source_sha256':sha(source),'candidate_sha256':sha(candidate),'stdout_sha256':sha(stdout),'type_axiom_audits':len(names),'full_signature_sha256':signatures,'seconds':seconds})
assert len(accepted)==r['fresh_current_host_kernel_modules']==39 and len(names_all)==len(set(names_all))==r['declaration_audits']==113
resource=[]
for name in r['modules']:
    d=json.loads((F/'resource-json'/(name+'.json')).read_bytes());assert d['samples']>0 and d['min_physical_KiB']>=1572864 and d['min_commit_free_KiB']>=524288
    resource.append(dict(module=name,worker_summary=d))
disk=json.loads((F/'resource-json/point-order-scoped-artifact-disk.json').read_bytes())
assert r['batches']['windows-point-order-20261009-01']['actual_execution_checkout_head']=='9489b759610e5026b9e5b8cb55ff40022b4e72c8'
assert r['batches']['windows-point-order-20261009-01']['scoped_artifact_disk_peak_bytes']==1487296294<2147483648
assert len([n for n in names_all if n.endswith('.base_order')])==1
assert r['inherited_primality_platform_validation']==dict(modules=38,declaration_audits=112,theorem_audits=75,definition_audits=37,new_primality_mathematical_results=0)
result=dict(schema='parent-concrete-base-order-existing-output-review-v1',files_rehashed=len(m['files']),dependency_references=depcounts,current_host_modules=accepted,exact_existing_type_axiom_pairs=113,inherited_primality_platform_audits=112,new_Point_order_audits=1,resource_summaries=resource,resource_sample_count_worker_report=sum(x['worker_summary']['samples'] for x in resource),raw_resources='Not transported; worker-derived JSON summaries retained with original sample SHA',scoped_disk_worker_summary=disk,guard_admission_batches=len(batch_inputs),kernel_runs=0,negative_control_credit=0,scope=r['proved_scope'],open=r['open'],full_transfer='OPEN')
(HERE/'packet-review01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='passed',files=len(m['files']),dependencies=depcounts,modules=39,existing_audits=113,inherited_platform=112,new_order=1)))
