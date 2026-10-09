"""Audit original immutable producer and export structured declaration outputs."""
import hashlib,json,re
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];O=R/'outputs/mac-poseidon-width6-upstream11'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=O/'publication-manifest01.json';e=O/'publication-envelope01.json'
assert sha(p)=='512fbc7dee19294af8180eb9c47dcb7dbe14ccaa56630a8b98e94af770795e24'
assert sha(e)=='2be900604f616bd59752ed5dc3c673cc2cf1adbce5e00db3c0e72f6d3ecf5762'
m=json.loads(p.read_text());env=json.loads(e.read_text())
assert env['producer_manifest']['sha256']==sha(p)
for x in m['files']+env['postseal_entries']:
    f=R/x['path'];assert sha(f)==x['sha256'] and f.stat().st_size==x['bytes'],x['path']
sources={Path(x['path']).stem:x for x in m['files'] if x['category'] in ['generated_instance','handwritten_helper']}
assert len(sources)==87 and set(sources)==set(m['receipts'])
copies=H/'sealed-owned-sources';assert not copies.exists();copies.mkdir()
for name,x in sources.items():(copies/(name+'.lean')).write_bytes((R/x['path']).read_bytes())
records=[];execution=[]
for name,x in sorted(m['receipts'].items()):
    receipt=R/x['receipt'];assert sha(receipt)==x['receipt_sha256'];j=json.loads(receipt.read_text());log=receipt.with_suffix('.log');assert sha(log)==j['log_sha256']
    assert j['status']=='passed' and j['exit']==0 and j['source_sha256']==x['source_sha256']==sources[name]['sha256'] and j['object_sha256']==x['object_sha256']
    obj=R/'work/mac-poseidon-width6-upstream11/project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean');assert sha(obj)==x['object_sha256']
    assert j['lean_heap_limit_MiB']==2048 and j['timeout_seconds']==240 and j['seconds']<=240 and '-j1' in j['command']
    assert j['process_group_rss_limit_bytes']==4*1024**3 and j['peak_group_rss_bytes']<=4*1024**3
    assert j['minimum_memory_free_percent']>=15 and j['minimum_disk_free_bytes']>=2*1024**3
    text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
    pairs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
    assert sorted(n for n,_ in pairs)==sorted(j['expected_axiom_names'])
    assert len(pairs)==x['audits']==j['axiom_audits']==len(j['full_signature_sha256'])
    for decl,value in pairs:
        axioms=[v.strip() for v in value.split(',') if v.strip()];assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
        hits=re.findall(r'^@?'+re.escape(decl)+r'(?:\.\{[^}\n]+\})?\s*:[\s\S]*?(?=^\''+re.escape(decl)+r'\')',text,re.M);assert len(hits)==1
        sig=hits[0].strip();assert hashlib.sha256(sig.encode()).hexdigest()==j['full_signature_sha256'][decl]
        records.append({'module':name,'declaration':decl,'pp_all_type':sig,'pp_all_type_sha256':j['full_signature_sha256'][decl],'axioms':axioms,'receipt_sha256':sha(receipt),'audited_source_sha256':j['source_sha256'],'raw_stdout_sha256':j['log_sha256']})
    execution.append({'module':name,'source_sha256':j['source_sha256'],'object_sha256':j['object_sha256'],'receipt_sha256':sha(receipt),'type_axiom_audits':len(pairs),'seconds':j['seconds'],'peak_group_rss_bytes':j['peak_group_rss_bytes']})
assert len(execution)==87 and len(records)==496
export={'schema':'parent-existing-kernel-stdout-structured-declaration-audit-v1','declarations':records,'raw_logs_retained_local_only':True,'new_Lean_executions':0,'full_transfer':'OPEN'}
out=H/'structured-type-axiom-audit01.json';assert not out.exists();out.write_text(json.dumps(export,indent=2)+'\n')
result={'schema':'parent-original-upstream11-seal-audit-v1','manifest_sha256':sha(p),'envelope_sha256':sha(e),'producer_entries_rehashed':len(m['files']),'postseal_entries_rehashed':len(env['postseal_entries']),'all_fresh_executions':87,'all_declaration_audits':496,'root_reachable_modules':85,'root_reachable_audits':491,'separate_probes':{'ImportFloor_True_marker_audits':1,'TailLeafProbe_audits':4},'failed_Lean_attempts_zero':11,'peak_group_rss_bytes':max(x['peak_group_rss_bytes'] for x in execution),'structured_type_axiom_audit_sha256':sha(out),'portable_hygiene_successor':'PENDING; originalrecipe retained immutable, no publication acceptance yet','executions':execution,'parent_kernel_runs':0,'full_transfer':'OPEN'}
out=H/'seal-audit01.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='executions'}))
