"""Rehash transported sources, reconstruct wrappers and parse existing audits."""
import datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];F=HERE/'frozen';REPO=ROOT/'work/shared-build-handoff';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((F/'manifest.json').read_text());r=json.loads((F/'receipt.json').read_text());d=json.loads((F/'dependency-resolution.json').read_text())
assert sha(F/'manifest.json')=='eed22b86348c79d195370dd4b770d56f39261d128f820f08d49f0de4fc50e7e3'
for n,x in m['files'].items():assert sha(F/n)==x['sha256'] and (F/n).stat().st_size==x['bytes']
assert r['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a' and r['mathlib_sha']=='c5ea00351c28e24afc9f0f84379aa41082b1188f' and r['lean_version']=='4.30.0'
assert r['actual_publication_checkout_head']=='8e55fc6550ca6ed0f4b7e81fa122f33c25fac4a0'
depcounts={'canonical':0,'packet_new':0}
for x in d:
    if x['reference_disposition']=='tracked at actual publication HEAD':
        assert sha(REPO/x['repository_reference'])==x['original_source_sha256']
        carried=F/'canonical-dependencies'/(x['name']+'.lean')
        if carried.exists():assert sha(carried)==x['original_source_sha256']
        depcounts['canonical']+=1
    else:assert sha(F/'maintained-source'/(x['name']+'.lean'))==x['original_source_sha256'];depcounts['packet_new']+=1
batch_inputs={}
for batch,b in r['batches'].items():
    p=F/'inputs'/batch;inputs=json.loads((p/'manifest.json').read_text());batch_inputs[batch]=inputs
    assert sha(p/'manifest.json')==b['source_manifest_sha256'] and b['actual_exit']==0
    recipe=b['recipe'];assert recipe['threads']==1 and recipe['memory_MiB']==1536 and recipe['finite_seconds_per_module']==240
    assert json.loads((p/'recipe.json').read_text())==recipe
    assert sha(F/'recipes'/('root-'+batch+'.ps1'))==recipe['guard_sha256'].lower()
    assert sha(F/'recipes'/('audit-'+batch+'.py'))==recipe['audit_sha256'].lower()
    admission=json.loads((p/'admission.json').read_text());assert admission['heavy_processes']==[] and admission['guard_sha256'].lower()==recipe['guard_sha256'].lower()
    assert admission['memory']['PhysicalKiB']>=3145728 and admission['memory']['CommitFreeKiB']>=2621440
    guard=(F/'recipes'/('root-'+batch+'.ps1')).read_text()
    assert "$env:LEAN_NUM_THREADS='1'" in guard and "'-j1','-M','1536'" in guard and 'finite-240s-budget' in guard and 'host-memory-pressure' in guard
accepted=[];names_all=[]
for name,leaf in r['modules'].items():
    inputs=batch_inputs[leaf['batch']];names=inputs['expected_theorems_by_module'][name];source=F/'maintained-source'/(name+'.lean');candidate=F/'audited-source'/(name+'.lean')
    assert sha(source)==inputs['sources'][name]['sha256'];body=source.read_text(encoding='utf-8-sig');end=list(re.finditer(r'(?m)^end\s+([\w.]+)\s*$',body))[-1].start()
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
assert len(accepted)==r['fresh_modules']==6 and len(names_all)==len(set(names_all))==r['declaration_audits']==67
result={'schema':'parent-eight-operation-sample-source-existing-stdout-review-v1','files_rehashed':len(m['files']),'dependency_references':depcounts,'fresh_modules':accepted,'exact_existing_full_types_and_axioms':67,'guard_admission_batches':len(batch_inputs),'raw_memory_logs':'not transported; exact guard/admission records and successful stdout inspected','prior_standard_model':'14modules54audits inherited separately, no fresh credit','failed_attempts':r['failed_attempts'],'kernel_runs':0,'negative_control_credit':0,'scope':r['proved_scope'],'open':r['open'],'full_transfer':'OPEN'}
(HERE/'packet-review01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','files':len(m['files']),'dependencies':depcounts,'modules':6,'existing_audits':67}))
