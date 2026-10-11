from pathlib import Path
import sys,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
p=S.parent/'mac-registry-gap145-data01/selected-data01.json';v=pin(p);require(v['sha256']=='ce453ccc4a8459dbbe645b9bd6377744fe981e99918b3f9d7aa30e377505af44'and v['bytes']==20175,'DATA');d=json.loads(p.read_bytes());P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def linear(ts,signed=False):return '['+','.join('('+str(x)+','+str(y-P if signed and y>P//2 else y)+')'for x,y in ts)+']'
def cases(key):return 'match index with\n'+''.join('  | '+str(i)+' => '+(linear(e[key],True)if key in['left','right']else str(e[key]))+'\n'for i,e in enumerate(d['entries']))+'  | _ => '+('[]'if key in['left','right']else'0')
t=(S/'template.lean').read_text();subs={'@ROWS@':'['+','.join('⟨'+linear(r['outlined_a'])+','+linear(r['outlined_b'])+'⟩'for r in d['arithmetic_rows'])+']','@LEFT@':cases('left'),'@RIGHT@':cases('right'),'@OUTPUT@':cases('output')}
for token,value in subs.items():require(t.count(token)==1,'unique placeholder');t=t.replace(token,value)
names=['arithmeticRows','left','right','output','auxiliary','sourceAt','rowCheck','row_checked','normalizedRows','pairCheck','productionCheck','production_checked','arithmetic_position','normalization_sound','products','gap_polynomial'];audits=['ShielddSecurity.CapturedRegistryGap145.'+n for n in names];t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits);require(len(t.encode())<=262144,'source');r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedRegistryGap145.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='CapturedRegistryGap145',source=pin(p),audits=audits)],generator=pin(Path(__file__)),template=pin(S/'template.lean'),data=v,scope='Six actual products12 arithmetic positions yield exact field gap polynomial under arbitrary rho and actual arithmetic rows. Explicit copy linkage transports actual outlined product rows to normalized rows. No gap assertion truth, legal RegistrySem, or desired order premise in this module.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
