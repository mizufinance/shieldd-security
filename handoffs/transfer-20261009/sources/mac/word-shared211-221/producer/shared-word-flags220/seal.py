from pathlib import Path
import json,hashlib,re,ast,runpy,os,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution245';S=W/'mac-shared-word-flags220-kernel-result01'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(v):require(pin(v['path'])==v,'exact original identity');return Path(v['path']).read_bytes()
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated sealer')
g=runpy.run_path(str(P/'maintained/guard.py'),run_name='read_config_only');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);inherited=json.loads(Path(c['closure']['path']).read_bytes())['modules'];inherited.update(c['qualified_batch_imports'])
raw=(P/'runtime/ledger.jsonl').read_bytes();events=[json.loads(x)for x in raw.splitlines()];current={}
for i,e in enumerate(events):
 if e['kind']=='result':
  r=json.loads(read(e['receipt']));current[r['module']]=(e['receipt'],i+1)
names=['SharedWordFlags220'];require(len(names)==1,'one shared map helper')
selected=[]
for n in names:
 rp=current[n][0]if n in current else inherited[n]['receipt'];r=json.loads(read(rp));require(r['status']=='passed'and type(r['exit'])is int and r['exit']==0 and r['error']is None and r['cleanup']['clean']and r['cleanup']['leader_reaped'],'every original module passed');selected.append((n,rp,r))
parser=ast.parse((P/'maintained/guard.py').read_text());nodes=[n for n in parser.body if isinstance(n,(ast.Import,ast.ImportFrom))or isinstance(n,ast.FunctionDef)and n.name in {'require','sha','_parse_audit_log'}];a={};exec(compile(ast.Module(body=nodes,type_ignores=[]),'exact original pure audit parser','exec'),a)
identities={};records=[];reports=[];replay=[]
for n,rp,r in selected:
 b=read(r['source']);root=Path(r['source']['path']).parents[2];spec=json.loads((root/'templates01.json').read_bytes());d=spec['modules'][n];expected=['ShielddSecurity.'+n+'.'+x for x in d['names']];actual=[x.decode()for x in re.findall(rb'^#check @([\w.]+)\s*$',b,re.M)];require(actual==expected,'exact complete public audit names');require(a['_parse_audit_log'](read(r['stdout']),expected)==r['audits']and read(r['stderr'])==b'','all complete raw type/std axioms match receipts')
 derived=(d['body']+'\n'+''.join('set_option pp.all true in\n#check @'+x+'\n#print axioms '+x+'\n'for x in expected)).encode();require(derived==b,'exact in-memory maintained byte replay')
 cache=Path(r['command'][r['command'].index('-o')+1]).parent;slots={}
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  path=cache/(n+suffix);v=r['objects'].get(str(path));slots[suffix]=v
  if v is None:require(not path.exists()and not path.is_symlink(),'exact absent companion')
 for v in [rp,r['source'],r['stdout'],r['stderr'],*r['objects'].values()]:read(v);identities[v['path']]=v
 for path,v in spec['inputs'].items():read(v);identities[path]=v
 for f in ['prepare.py','generate.py','templates01.json','generation01.json','producer-manifest01.json','envelope01.json','postseal-guard01.json']:
  v=pin(root/f);identities[v['path']]=v
 records.append(dict(module=n,source=r['source'],objects=r['objects'],companions=slots,receipt=rp,stdout=r['stdout'],stderr=r['stderr'],original_ordinal=r['all_attempts'],seconds=r['lean_seconds'],peak_group_rss=r['peak_group_rss'],cleanup=r['cleanup'],audits=expected,inherited_closure=r['inherited_closure'],official_manifest=r['official_manifest']));reports+=r['audits'];replay.append(dict(module=n,templates=pin(root/'templates01.json'),source=r['source'],bytes=len(b),reports=len(expected)))
require(len(reports)==8 and len({r['name']for r in reports})==8,'exact8 original reports')
end=current['SharedWordFlags220'][1];prefix=events[:end];require(prefix[-1]['receipt']==records[-1]['receipt']and end%2==0,'exact balanced root endpoint prefix');require(not S.exists(),'new immutable endpoint');v=os.statvfs(W);require(v.f_bavail*v.f_frsize>=2*1024**3+4*1024**2,'safe small endpoint disk reserve');S.mkdir()
put('source-object-receipt01.json',records);put('full-audits01.json',reports);put('byte-replay01.json',dict(method='Independent in-memory frozen maintained literal-body plus exact full-audit suffix; no Lean replay or second physical source copies',modules=replay));put('ledger-prefix01.json',dict(events=prefix,carried=c['carried_failure'],carried_attempts=c['carried_attempts'],endpoint_attempt=records[-1]['original_ordinal'],scope='Only balanced immutable ledger prefix ending at root209; later jobs may append'))
put('scope01.json',dict(modules=1,reports=8,runtime=c['runtime_sha'],source_context=c['canonical_context'],guard=pin(P/'maintained/guard.py'),claims=['Constructs one Boolean map with each requested word encoding under explicit shared-column agreement','Fallback bits preserved outside assignment keys; no row-truth or desired-hash premises'],open=['Actual overlap and parity agreement must be derived from legal input meanings','Captured shared witness, complete legal seed, native/full Transfer/final integrated replay'],failed_history_preserved=True))
put('dependencies01.json',dict(inputs=identities,current_config=pin(P/'config01.json'),history=c['carried_failure'],closure=c['closure'],storage_map=g['_STORAGE_PIN']));(S/'seal.py').write_bytes(Path(__file__).read_bytes());put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),original_inputs=identities));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(dict(stage=str(S),modules=1,reports=8,producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),bytes=sum(p.stat().st_size for p in S.iterdir()))))
