import pathlib,json,hashlib,re,datetime
if not __debug__:raise RuntimeError('optimized mode forbidden')
repo=pathlib.Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/shared-build-handoff');packet=repo/'handoffs/transfer-20261009/sources/windows/concrete-field-20261009-01';receipt=repo/'handoffs/transfer-20261009/receipts/windows/concrete-field-20261009-01.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((packet/'manifest.json').read_text());r=json.loads(receipt.read_text());assert sha(packet/'manifest.json')==r['source_packet_manifest_sha256']
for rel,f in m['files'].items():
 p=packet/rel;assert sha(p)==f['sha256'] and p.stat().st_size==f['bytes'],rel
for name,h in m['canonical_generated'].items():assert sha(repo/'circuits/ShielddSecurity'/f'{name}.lean')==h,name
for p in (packet/'handwritten').glob('*.lean'):assert p.read_bytes()==(repo/'circuits/ShielddSecurity'/p.name).read_bytes(),p.name
assert m['candidate_sha256']=='20d3da8789fc847a4e5450c430321b52350e79f7533bcd43ff48695ffa4c862d'
assert sha(repo/'handoffs/transfer-20261009/sources/parent/field-certificate-inputs01/candidate.json')==m['candidate_sha256']
strip=lambda s:re.sub(r'(?m)^(?:set_option pp\.all true in\r?\n)?#(?:check|print axioms)[^\r\n]*\r?\n','',s)
def source(name):return packet/'upstream/Mathlib/NumberTheory/LucasPrimality.lean' if name=='UpstreamLucasPrimality' else repo/'circuits/ShielddSecurity'/f'{name}.lean'
phases=[];all_deps=set();audit_count=0
for key,filename in [('pilot05','windows-field-certificate-pilot-20261009-05.json'),('tree03','windows-field-certificate-tree-20261009-03.json'),('concrete01','windows-field-concrete-20261009-01.json')]:
 inp=packet/'inputs'/filename;v=json.loads(inp.read_text());rr=r['runs'][key];assert sha(inp)==rr['manifest_sha256'];assert rr['actual_exit']==0 and rr['root_resume_status']==0
 for name,q in v['sources'].items():assert sha(source(name))==q['sha256'];all_deps.add(name)
 for q in v.get('reused',[]):assert sha(source(q['name']))==q['original_source_sha256'];all_deps.add(q['name'])
 count=0
 for name,names in v['expected_theorems_by_module'].items():
  p=source(name);body=strip(p.read_text(encoding='utf-8-sig'));assert re.findall(r'^theorem\s+(\w+)',body,re.M)==names
  ends=list(re.finditer(r'(?m)^end\s+([\w.]+)\s*$',body));at=ends[-1].start() if ends else len(body)
  audits=''.join(f'\nset_option pp.all true in\n#check @{n}\n#print axioms {n}\n' for n in names)
  candidate=body[:at]+audits+body[at:];h=hashlib.sha256(candidate.encode()).hexdigest();assert h==v['audited_candidates'][name],name
  leaf=rr['modules'][name];a=leaf['audit'];assert leaf['actual_exit']==0 and a['original_source_sha256']==sha(p) and a['candidate_sha256']==h and a['full_types_checked'] is True
  assert len(a['axioms'])==a['audits']==len(names)
  for short in names:
   hits=[n for n in a['axioms'] if n==short or n.endswith('.'+short)];assert len(hits)==1
   assert set(a['axioms'][hits[0]])<={'propext','Classical.choice','Quot.sound'}
  count+=len(names)
 assert count==rr['audits'];audit_count+=count;phases.append({'phase':key,'fresh_modules':len(v['expected_theorems_by_module']),'audits':count,'audited_sources_reconstructed':True})
assert audit_count==r['theorem_audits']==106
assert all(x['proof_and_control_credit']==0 for x in r['failed_staging'].values())
out={'kind':'parent-transport-source-and-reported-audit-review','observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':'392ea6c7527b807a3a223e7a7507e3bfe73ea5ff','manifest_sha256':sha(packet/'manifest.json'),'receipt_sha256':sha(receipt),'transport_files_verified':len(m['files']),'canonical_generated_verified':len(m['canonical_generated']),'canonical_dependency_sources_verified':len(all_deps),'phases':phases,'reported_theorem_audits_checked':audit_count,'local_raw_logs_available':False,'independent_log_reaudit':False,'kernel_rerun':False,'limits':['Audited source candidates reconstructed exactly and receipt axiom/name claims checked. Raw Windows logs are not present locally; no independent replay or full-type-log re-audit claimed.','Native codec/FFI, full curve model, subgroup-order primality and global curve order remain open.'],'full_transfer':'OPEN'}
(pathlib.Path(__file__).parent/'packet-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'passed','files':out['transport_files_verified'],'generated':out['canonical_generated_verified'],'dependency_sources':out['canonical_dependency_sources_verified'],'audits':audit_count}))
