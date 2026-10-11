from pathlib import Path
import ast,json,hashlib,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution223';S=W/'mac-threecall-global-binding173-kernel-result01'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def checked(v):require(pin(v['path'])==v,'exact original pin '+v['path']);return Path(v['path']).read_bytes()
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
c=json.loads((P/'config01.json').read_bytes());owned={n:d for n,d in c['qualified_batch_imports'].items()if n.startswith('CapturedThreeCallGlobalBinding173')}
for number,n in [(1186,'CapturedThreeCallGlobalBinding173J104'),(1187,'CapturedThreeCallGlobalBinding173')]:
 rp=P/'runtime/receipts'/f'{number}-{n}.json';r=json.loads(rp.read_bytes());cache=Path(r['command'][r['command'].index('-o')+1]).parent
 owned[n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=pin(rp),current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']})
require(len(owned)==144,'exact whole binding144 source modules')
# Independently reparse original RAW type/standard axiom records; no executor.
text=(P/'maintained/guard.py').read_text();tree=ast.parse(text);body=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom))or isinstance(n,ast.FunctionDef)and n.name in {'require','sha','_parse_audit_log'}];g={};exec(compile(ast.Module(body=body,type_ignores=[]),'selected-exact-audit-parser','exec'),g)
records=[];roots=set();replay=[];identities={};summary=[]
for n,d in sorted(owned.items()):
 r=json.loads(checked(d['receipt']));source=checked(d['source']);require(r['status']=='passed'and type(r['exit'])is int and r['exit']==0 and r['error']is None and r['cleanup']['clean']and r['cleanup']['leader_reaped'],'exact accepted receipt/cleanup')
 require(r['source']==d['source']and r['objects'][d['object']['path']]==d['object'],'source/object/receipt association')
 names=re.findall(rb'^#check @([A-Za-z0-9_.]+)\s*$',source,re.M);names=[v.decode()for v in names]
 require(g['_parse_audit_log'](checked(r['stdout']),names)==r['audits'],'complete original type/axiom equality')
 require(checked(r['stderr'])==b'','original empty stderr')
 for v in [d['source'],d['receipt'],r['stdout'],r['stderr'],*r['objects'].values()]:checked(v);identities[v['path']]=v
 for suffix,v in d['current_slots'].items():
  path=Path(d['object']['path']).with_name(n+suffix)
  if v is None:require(not path.exists()and not path.is_symlink(),'exact companion absence')
  else:require(pin(path)==v,'exact companion identity')
 root=Path(d['source']['path']).parents[2];roots.add(root)
 template=root/(n+'.template.lean');require(template.is_file(),'actual maintained template exists')
 derived=template.read_text()+'\n'+''.join('set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'for name in names)
 require(derived.encode()==source,'maintained template source byte replay')
 replay.append(dict(module=n,template=pin(template),source=d['source'],bytes=len(source),audit_count=len(names)))
 summary.append(dict(module=n,source=d['source'],object=d['object'],companions=d['current_slots'],receipt=d['receipt'],stdout=r['stdout'],stderr=r['stderr'],original_ordinal=r['all_attempts'],seconds=r['lean_seconds'],peak_group_rss=r['peak_group_rss'],cleanup=r['cleanup'],audits=names));records+=r['audits']
 for v in [pin(template),pin(root/'generate.py'),pin(root/'generation01.json')]:identities[v['path']]=v
require(len(records)==867 and len({r['name']for r in records})==867,'exact867 unique complete reports')
# Live new receipts may append; freeze only the immutable two-result prefix.
events=[json.loads(x)for x in(P/'runtime/ledger.jsonl').read_bytes().splitlines()];prefix=events[:4]
require(len(prefix)==4 and prefix[3]['receipt']['path']==str(P/'runtime/receipts/1187-CapturedThreeCallGlobalBinding173.json'),'exact accepted endpoint ledger prefix')
require(not S.exists(),'new immutable result');disk=os.statvfs(W);require(disk.f_bavail*disk.f_frsize>=2*1024**3+8*1024**2,'disk reserve before small endpoint seal');S.mkdir()
put('source-object-receipt01.json',summary);put('full-audits01.json',records);put('byte-replay01.json',dict(method='Independent in-memory maintained literal template plus exact check/print suffix; no original driver or second physical source copy',modules=replay,formal_credit=0))
put('ledger-snapshot01.json',dict(events=prefix,carried_failure=c['carried_failure'],carried_attempts=c['carried_attempts'],endpoint_attempts=1187,endpoint_failed=124,scope='Exact historical originals plus first two current immutable result records; live dispatcher may append Boolean jobs'))
put('scope01.json',dict(modules=144,complete_reports=867,arithmetic_positions=1572,shared_copy_positions=1,captured_indices='734..2305 inclusive and200769',antecedent='Full indexed SatisfiesAt rho CapturedFullRelation58.rowAt200770; explicit Field/CharP roles from exact original full types',conclusion='Captured ordered arithmeticRows and copy row satisfied on same arbitrary rho; no local-row or desired-hash truth premises',constructor_scope='Existing1467-distinct-assertion shared constructor unchanged; this is full-relation soundness selection binding',open=['Remaining global registry/path bindings','Independent total legal-input constructor/all assertions','Actual native correspondence','Full Transfer'],runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',canonical_notice='9150f792bcd2e60afdd3acc879824b36282fd953',guard=pin(P/'maintained/guard.py'),new_guard_delta=pin(W/'mac-resource-preflight222-source01/producer-manifest01.json'),failed_prior_history_unchanged=True,portable_generation='Maintained templates/generators transported as exact original references; a relocated complete import/generation package remains integration work. No combined proof replay claim.'))
(S/'seal.py').write_bytes(Path(__file__).read_bytes());(S/'failed-census-attempt01.py').write_bytes(Path('/tmp/seal_join173_attempt01.py').read_bytes());put('failed-census-observation01.json',dict(scope='ZERO_CREDIT_DATA_PREWRITE_REFUSAL',reason='Expected866 instead of actual867 exact complete declaration reports; J104 has6 reports, not5. Corrected only sealer census, no Lean/source/object/receipt changed.')); put('source-dependencies01.json',dict(roots=sorted(str(p)for p in roots),current_configuration=pin(P/'config01.json'),carried_history=c['carried_failure'],storage_map=dict(path=str(W/'mac-history-metadata-preservation126-28/archive-map01.json'),**{k:v for k,v in pin(W/'mac-history-metadata-preservation126-28/archive-map01.json').items()if k!='path'}),identity_records=identities))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),endpoint_inputs=identities));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),modules=144,reports=867,producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),bytes=sum(p.stat().st_size for p in S.iterdir()),active_dispatcher_untouched=True)))
