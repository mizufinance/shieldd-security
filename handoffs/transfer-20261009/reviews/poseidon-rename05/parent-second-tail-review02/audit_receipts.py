import pathlib,json,hashlib,importlib.util
if not __debug__:raise RuntimeError('optimized mode forbidden')
root=pathlib.Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');src=root/'work/mac-poseidon-rename05';out=root/'outputs/mac-poseidon-rename05';dst=pathlib.Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
a=src/'audit_log.py';spec=importlib.util.spec_from_file_location('pilot_log_audit',a);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
manifest=out/'publication-manifest01.json'; sealed=json.loads(manifest.read_text())
assert sha(manifest)=='a202d35cd4e24e824731153408b341a1d1fc4bd76298e9e90d3bda142f850ada'
for entry in sealed['files']:
 f=root/entry['path'];assert sha(f)==entry['sha256'] and f.stat().st_size==entry['bytes'],str(f)
results=[]
for module,entry in sealed['current_pass_receipts'].items():
 p=root/entry['path'];assert sha(p)==entry['sha256'];d=json.loads(p.read_text());assert sha(a)==d['guard_sources_sha256']['audit_log.py']
 log=p.with_suffix('.log');assert sha(log)==d['log_sha256'];assert sha(src/'project/ShielddSecurity'/f'{module}.lean')==d['source_sha256']
 assert d['status']=='passed' and d['exit']==0;assert '-j1' in d['command'] and '-M2048' in d['command'];assert d['timeout_seconds']==240 and d['process_group_rss_limit_bytes']==4294967296;imports=0
 for dep,v in d['frozen_imports'].items():
  if dep.startswith('ShielddSecurity.'):
   f=src/'project'/pathlib.Path(*dep.split('.')).with_suffix('.lean');assert sha(f)==v['source_sha256'],dep;imports+=1
  elif dep=='package':
   for name,key in [('lakefile.lean','lakefile_sha256'),('lake-manifest.json','lake_manifest_sha256'),('lean-toolchain','toolchain_sha256')]:assert sha(src/'project'/name)==v[key],name
  elif dep=='mathlib_revision':assert v=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
  elif dep=='official_import_closure':assert sha(out/v['manifest_file'])==v['manifest_sha256']
  else:raise RuntimeError('unknown dependency metadata '+dep)
 r=m.validate(log.read_text(),d['expected_axiom_names'],d['expected_signature_names']);assert r['axiom_audits']==d['axiom_audits'] and r['full_signature_sha256']==d['full_signature_sha256']
 results.append({'module':module,'receipt_sha256':sha(p),'source_sha256':d['source_sha256'],'log_sha256':d['log_sha256'],'axiom_audits':r['axiom_audits'],'frozen_import_source_hashes_checked':imports})
r={'kind':'parent-exact-log-and-source-reaudit-no-new-kernel-run','auditor_sha256':sha(a),'modules':results,'total_audits':sum(x['axiom_audits'] for x in results),'source_review_snapshot_compatible':True,'kernel_rerun':False,'packet_sealed':True,'sealed_entries_rehashed':len(sealed['files']),'publication_entries':sum(x['publication'] for x in sealed['files']),'manifest_sha256':sha(manifest),'previous_parent_attempts':[],'failed_attempts_credit':0,'full_transfer':'OPEN'};(dst/'receipt-audit.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS total',r['total_audits'])
