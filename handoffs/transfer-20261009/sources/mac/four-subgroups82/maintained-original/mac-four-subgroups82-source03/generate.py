from pathlib import Path
import json,hashlib,re,sys
S=Path(__file__).resolve().parent
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with (S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
require(not(S/'source-root').exists()and not(S/'producer-manifest01.json').exists(),'immutable generation')
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);outputs=[]
def emit(name,namespace,text,count):
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',text,re.M);require(len(names)==len(set(names))==count,'exact declaration inventory '+name)
 text+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{namespace}.{n}\n#print axioms ShielddSecurity.{namespace}.{n}\n'for n in names)
 p=r/(name+'.lean');p.write_text(text);outputs.append(dict(name=name,source=pin(p),audits=['ShielddSecurity.'+namespace+'.'+n for n in names]))
emit('CapturedFourSubgroups82Core','CapturedFourSubgroups82',(S/'core-template.lean').read_text(),10)
for i in range(3):
 name=f'CapturedFourSubgroups82Check0{i+1}';text=f'import ShielddSecurity.CapturedFourSubgroups82Core\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnamespace ShielddSecurity.{name}\ntheorem checked : CapturedFourSubgroups82.rowCheck ⟨{i},by decide⟩=true := by decide +kernel\nend ShielddSecurity.{name}\n';emit(name,name,text,1)
emit('CapturedFourSubgroups82','CapturedFourSubgroups82',(S/'main-template.lean').read_text(),2)
put('generation01.json',dict(generator=pin(Path(__file__)),templates=[pin(S/'core-template.lean'),pin(S/'main-template.lean')],outputs=outputs,scope='UNRUN SOURCE: exact other-three selected original-row transport; all four source preimage curves and three-doubling conclusions from full captured SAT. Actual model/native/global legal construction OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(dict(outputs=[x['name']for x in outputs])))
