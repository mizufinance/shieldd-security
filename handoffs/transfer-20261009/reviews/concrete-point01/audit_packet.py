import pathlib,json,hashlib,re
if not __debug__:raise RuntimeError('optimized mode forbidden')
repo=pathlib.Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/shared-build-handoff')
packet=repo/'handoffs/transfer-20261009/sources/windows/concrete-point-20261009-01'
receipt=repo/'handoffs/transfer-20261009/receipts/windows/concrete-point-20261009-01.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((packet/'manifest.json').read_text());r=json.loads(receipt.read_text());assert sha(packet/'manifest.json')==r['source_packet_manifest_sha256']
for rel,v in m['files'].items():
 p=packet/rel;assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],rel
resolution=json.loads((packet/'dependency-resolution.json').read_text())
for name,v in resolution.items():assert sha(repo/v['path'])==v['sha256'],name
strip=lambda s:re.sub(r'(?m)^(?:set_option pp\.all true in\r?\n)?#(?:check|print axioms)[^\r\n]*\r?\n','',s)
names_all=[];results=[];theorems=definitions=0
for phase,run in r['runs'].items():
 inp=packet/'inputs'/f'{phase}.json';v=json.loads(inp.read_text());assert sha(inp)==run['manifest_sha256']
 assert run['actual_exit']==run['root_resume_status']==0
 for name,x in v['sources'].items():assert sha(repo/'circuits/ShielddSecurity'/f'{name}.lean')==x['sha256']
 for x in v['reused']:assert sha(repo/resolution[x['name']]['path'])==x['original_source_sha256']
 for name,names in v['expected_theorems_by_module'].items():
  p=repo/'circuits/ShielddSecurity'/f'{name}.lean';assert (packet/'circuits/ShielddSecurity'/p.name).read_bytes()==p.read_bytes();body=strip(p.read_text(encoding='utf-8-sig'))
  decls=re.findall(r'^(?:noncomputable )?(theorem|def)\s+(\w+)',body,re.M)
  assert all(n in names for k,n in decls if k=='theorem')
  decls=[(k,n)for k,n in decls if n in names];assert [n for _,n in decls]==[n for n in names if '.' not in n],(name,decls,names)
  theorems+=sum(k=='theorem'for k,_ in decls);definitions+=sum(k=='def'for k,_ in decls)
  end=list(re.finditer(r'(?m)^end\s+([\w.]+)\s*$',body))[-1].start()
  checks=''.join(f'\nset_option pp.all true in\n#check @{n}\n#print axioms {n}\n'for n in names)
  audited=body[:end]+checks+body[end:];h=hashlib.sha256(audited.encode()).hexdigest();assert h==v['audited_candidates'][name],name
  leaf=run['modules'][name];a=leaf['audit'];assert leaf['actual_exit']==0 and a['original_source_sha256']==sha(p) and a['candidate_sha256']==h and a['full_types_checked']
  assert len(names)==a['audits']==len(a['axioms'])
  for n in names:
   hits=[k for k in a['axioms']if k==n or k.endswith('.'+n)];assert len(hits)==1
   assert set(a['axioms'][hits[0]])<={'propext','Classical.choice','Quot.sound'};names_all+=hits
  results.append({'module':name,'declarations':len(names),'source_sha256':sha(p),'reconstructed_audited_sha256':h})
assert len(results)==r['fresh_local_modules']==3 and len(names_all)==len(set(names_all))==r['declaration_audits']==30
assert theorems+definitions==26 and r['cached_foreign_declaration_audits']==4
out={'kind':'parent-source-transport-and-reported-audit-review','source_commit':'677e1a85bfb23c98a618c55f7967d75e3b9d114b','packet_manifest_sha256':sha(packet/'manifest.json'),'receipt_sha256':sha(receipt),'transport_files_verified':len(m['files']),'canonical_dependency_sources':len(resolution),'fresh_modules':results,'distinct_audited_declarations':len(names_all),'local_theorems':theorems,'local_definitions':definitions,'cached_foreign_audits':4,'independent_raw_log_reaudit':False,'kernel_rerun':False,'prior_parent_inspection_failure':'Initially assumed all reused sources were canonical ShielddSecurity files; UpstreamLucasPrimality resolves through explicit dependency-resolution to the pinned upstream source. Failed inspection had zero credit.','scope':'Concrete Edwards Parameters, exact Mathlib discriminant/ellipticity, full Point-set bijection and identity/torsion images. Addition/StandardCurveModel/order/native OPEN.','full_transfer':'OPEN'}
(pathlib.Path(__file__).parent/'packet-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'passed','files':len(m['files']),'dependencies':len(resolution),'declarations':len(names_all)}))
