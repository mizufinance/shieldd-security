from pathlib import Path
import ast,json,hashlib,re,os,lzma
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-captured-canonical217-kernel-result01';P=W/'mac-full-arithmetic45-execution234'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(v):require(pin(v['path'])==v,'exact original pin');return Path(v['path']).read_bytes()
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
wrapped=json.loads((P/'config01.json').read_bytes());m=json.loads((W/'mac-history-metadata-preservation126-35/archive-map01.json').read_bytes())['records'];record=m[wrapped['base']['path']];packed=read(record['archive']);decoder=lzma.LZMADecompressor();base=decoder.decompress(packed,max_length=wrapped['base']['bytes']+1);require(decoder.eof and not decoder.unused_data and len(base)==wrapped['base']['bytes']and hashlib.sha256(base).hexdigest()==wrapped['base']['sha256'],'exact archived base');c=json.loads(base);c.update(wrapped['replace']);
for k,v in wrapped['merge'].items():c[k].update(v)
require(hashlib.sha256((json.dumps(c,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()==wrapped['effective_sha256'],'exact effective config')
selected=[(P/'runtime/receipts/1234-CapturedCanonical217.json',W/'mac-captured-canonical217-source02')]
guard=(P/'maintained/guard.py').read_text();tree=ast.parse(guard);nodes=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom))or isinstance(n,ast.FunctionDef)and n.name in {'require','sha','_parse_audit_log'}];a={};exec(compile(ast.Module(body=nodes,type_ignores=[]),'exact original pure audit parser','exec'),a)
summary=[];audits=[];identities={};replay=[]
for rp,root in selected:
 r=json.loads(rp.read_bytes());require(r['status']=='passed'and type(r['exit'])is int and r['exit']==0 and r['error']is None and r['cleanup']['clean']and r['cleanup']['leader_reaped'],'actual accepted receipt')
 b=read(r['source']);names=[x.decode()for x in re.findall(rb'^#check @([A-Za-z0-9_.]+)\s*$',b,re.M)]
 require(a['_parse_audit_log'](read(r['stdout']),names)==r['audits']and read(r['stderr'])==b'','exact RAW full reports and empty stderr')
 for v in [pin(rp),r['source'],r['stdout'],r['stderr'],*r['objects'].values()]:read(v);identities[v['path']]=v
 spec=json.loads((root/'templates01.json').read_bytes());d=spec['modules'][r['module']]
 derived=(d['body']+'\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in names)).encode();require(derived==b,'maintained template exact in-memory source replay')
 require(names==['ShielddSecurity.'+r['module']+'.'+n for n in d['names']],'complete explicit audit-name census')
 for path,v in spec['inputs'].items():read(v);identities[path]=v
 for f in ['prepare.py','generate.py','templates01.json','generation01.json','producer-manifest01.json','envelope01.json','postseal-guard01.json']:
  v=pin(root/f);identities[v['path']]=v
 replay.append(dict(module=r['module'],templates=pin(root/'templates01.json'),source=r['source'],bytes=len(b),reports=len(names)))
 cache=Path(r['command'][r['command'].index('-o')+1]).parent
 slots={}
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  path=cache/(r['module']+suffix);v=r['objects'].get(str(path));slots[suffix]=v
  if v is None:require(not path.exists()and not path.is_symlink(),'exact companion absence')
 summary.append(dict(module=r['module'],source=r['source'],objects=r['objects'],companions=slots,receipt=pin(rp),stdout=r['stdout'],stderr=r['stderr'],original_ordinal=r['all_attempts'],seconds=r['lean_seconds'],peak_group_rss=r['peak_group_rss'],cleanup=r['cleanup'],audits=names,inherited_closure=r['inherited_closure'],official_manifest=r['official_manifest']))
 audits+=r['audits']
require(len(audits)==5 and len({x['name']for x in audits})==5,'exact5 reports')
failed=W/'mac-full-arithmetic45-execution233/runtime/receipts/1233-CapturedCanonical217.json';f=json.loads(failed.read_bytes());require(f['status']=='failed'and f['fresh_execution_credit']==0 and f['cleanup']['clean'],'immutable failed tag whole-module zero')
for v in [pin(failed),f['source'],f['stdout'],f['stderr']]:read(v);identities[v['path']]=v
raw=(P/'runtime/ledger.jsonl').read_bytes();events=[json.loads(x)for x in raw.splitlines()];require(len(events)>=2 and events[1]['receipt']==summary[0]['receipt'],'exact current first-result immutable prefix')
require(not S.exists(),'new immutable endpoint');disk=os.statvfs(W);require(disk.f_bavail*disk.f_frsize>=2*1024**3+2*1024**2,'disk safety reserve for small endpoint');S.mkdir()
put('source-object-receipt01.json',summary);put('full-audits01.json',audits);put('byte-replay01.json',dict(method='Independent in-memory maintained literal body plus complete exact #check/#print suffix; no Lean or second physical source copy',modules=replay))
put('ledger-prefix01.json',dict(events=events[:2],carried=c['carried_failure'],carried_attempts=c['carried_attempts'],endpoint_attempts=1234,endpoint_failures=128,scope='All original protected histories plus only first two current immutable ledger events. Dispatcher may append Boolean/word jobs.'))
put('scope01.json',dict(modules=1,reports=5,runtime=c['runtime_sha'],source_context=c['canonical_context'],publication_notice='3fecf17cc8587e9d84d92d7b228283aec1f54525',guard=pin(P/'maintained/guard.py'),claims=['Full captured relation derives actual Boolean bits/reconstruction/selected arithmetic row truth and actual terminal acceptance via finite syntax/position checks; these feed canonical recovery without desired hash/canonical truth premises'],not_claimed=['Concrete14 captured comparison instance coverage or terminal/max parameter binding','Total legal witness/full assertions/full Transfer/native refinement'],constructor_assertion_scope_unchanged=1467,failed_source01=dict(receipt=pin(failed),whole_module_credit=0),portable_generation='Maintained exact body/generator references; full relocated import/generation closure remains integration work.'))
put('dependencies01.json',dict(inputs=identities,current_config=pin(P/'config01.json'),history=c['carried_failure'],closure=c['closure'],storage_map=pin(W/'mac-history-metadata-preservation126-35/archive-map01.json')))
(S/'seal.py').write_bytes(Path(__file__).read_bytes());put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),original_inputs=identities));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),modules=1,reports=5,producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),bytes=sum(p.stat().st_size for p in S.iterdir()),active_dispatcher_untouched=True)))
