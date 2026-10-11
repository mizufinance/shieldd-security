# Immutable balanced exact assertion-provider composition.
from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent
Q=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-assertion-provider50-source01/qualification01.json')
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized Python')
require(not(S/'generation01.json').exists()and not(S/'source-root').exists(),'immutable emission')
require(pin(Q)['sha256']=='76342258e7741b9f7863117c4784161329e4be86910bbf57388fcafa589cc9c6','qualification pin before loading')
T=S/'template.lean';require(pin(T)['sha256']=='84aad25474a902c378c32b079c6b0e683ea6530585125f79a13a4d779f4adde1','exact maintained template');t=T.read_text();chunks=json.loads(Q.read_bytes())['chunks']
root=S/'source-root/ShielddSecurity';root.mkdir(parents=True);outputs=[];groups=[]
def combine(items):
 if len(items)==1:return items[0][0],items[0][1]
 m=len(items)//2;a,n=combine(items[:m]);b,k=combine(items[m:]);return f'(CompilerAssertionBlock51.append p copy {n} {k} {a} {b})',n+k
def emit(name,items,imports,extra=''):
 b,n=combine(items);text=''.join('import ShielddSecurity.'+i+'\n'for i in imports)+t.replace('NAME',name).replace('LENGTH',str(n)).replace('BLOCK',b)
 if extra:text=text.replace('end ShielddSecurity.'+name,extra+'end ShielddSecurity.'+name)
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',text,re.M);text+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{v}\n#print axioms ShielddSecurity.{name}.{v}\n'for v in names)
 require(len(text.encode())<=262144,'finite source size');p=root/(name+'.lean')
 with p.open('x')as f:f.write(text)
 outputs.append(dict(name=name,source=pin(p),audits=['ShielddSecurity.'+name+'.'+v for v in names],length=n));return name+'.block',n
for start in range(0,len(chunks),16):
 segment=chunks[start:start+16];names=['CapturedAssertions50B'+str(v['index']).zfill(4)for v in segment];groups.append(emit('CapturedAssertions54G'+str(start//16).zfill(2),[(n+'.block',v['count'])for n,v in zip(names,segment)],names))
require(sum(v[1]for v in groups)==22816,'all22813assertions+3actualverifierlinks')
extra='''noncomputable def rowAt := block.actual
noncomputable def recipeAt := block.recipe
theorem every_position (index : Nat) (bound : index<22816) : ∃ row,rowAt index=some row :=
  CompilerAssertionBlock51.every_position p copy 22816 block index bound
variable {F : Type} [Field F] [CharP F p]
theorem satisfies_iff (rho : Nat → F) (linked : rho copy=rho 0) :
    CompilerAssertionBlock51.SatisfiesAt rho rowAt 22816 ↔
    CompilerAssertionBlock51.TruthAt rho recipeAt 22816 :=
  CompilerAssertionBlock51.satisfies_iff copy 22816 block rho linked
'''
emit('CapturedFullAssertions54',groups,[name.split('.')[0]for name,_ in groups],extra)
with(S/'generation01.json').open('x')as f:f.write(json.dumps(dict(qualification=pin(Q),template=pin(T),generator=pin(Path(__file__)),outputs=outputs,scope='Unrun exact indexed provider: source-LC assertion equality only; copy premise separately derives from actual verifier-link row, not legal-input semantic truth.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(modules=len(outputs),source_bytes=sum(v['source']['bytes']for v in outputs))))
