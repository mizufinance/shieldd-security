from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def lin(ts):return '['+','.join(f'({c},{v})'for c,v in ts)+']'
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
D=S/'selected-data01.json';require(pin(D)['sha256']=='4f8a5258a15a7d886cf946a596ba14c866f93acc3ea177746a7744169dcdb0af','immutable DATA')
d=json.loads(D.read_bytes());n='CapturedIndexedArithmetic40Block512';actual=[d['actual_outlined'][str(i)]for i in range(512)];cp=d['actual_outlined']['200769'];require(d['low']==22738 and d['count']==512 and len(d['recipes'])==320,'instance shape')
CD=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-arithmetic-coefficients39-source01/coefficients01.json')
cb=CD.read_bytes();require(hashlib.sha256(cb).hexdigest()=='2de49e8a330defea76d11c36645b29a85f254c639166e71e286b3745cfa81332','exact coefficient index')
cs=json.loads(cb)['coefficients'];ids={v:i for i,v in enumerate(cs)}
def encoded(ts):return '['+','.join(f'({c},{ids[v]})'for c,v in ts)+']'
def actualLinear(index):return '(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (inputs '+str(index)+'))'
t="import ShielddSecurity.CompilerIndexedRecipe38\nimport ShielddSecurity.ArithmeticCoefficients39\nimport ShielddSecurity.CompilerIndexedCoverage36\nimport ShielddSecurity.CompilerArithmeticTransport41\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.CapturedIndexedArithmetic40Block512\nopen Compiler CompilerIndexed01\nopen CompilerArithmeticTransport41 (p copy)\n"
def tree(lo,hi):
 if hi-lo==1:return encoded(actual[lo]['a'])
 mid=(lo+hi)//2
 return '(if index<'+str(mid)+' then '+tree(lo,mid)+' else '+tree(mid,hi)+')'
t+='def inputs (index : Nat) : CompilerIndexedRecipe38.Terms := '+tree(0,len(actual))+'\n'
t+='def arithmetic : Array Row := (Array.mk ['+','.join('⟨'+actualLinear(i)+','+lin(x['b'])+'⟩'for i,x in enumerate(actual))+'])\n'
t+='def actualCopy : Row := ⟨'+lin(cp['a'])+','+lin(cp['b'])+'⟩\n'
refs=[]
for r in d['recipes']:
 j=r['relative'];refs.append('.square (inputs '+str(j)+')' if r['kind']=='square'else '.pair (inputs '+str(j)+') (inputs '+str(j+1)+')')
t+='def recipes : List CompilerIndexedRecipe38.Recipe := ['+','.join(refs)+']\n'
t+=(S/'template.lean').read_text()
t=re.sub(r'(?m)^def ', 'noncomputable def ',t)
names=re.findall(r'^\s*(?:noncomputable )?(?:def|theorem) ([\w.]+)',t,re.M);t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{n}.{x}\n#print axioms ShielddSecurity.{n}.{x}\n'for x in names if True)
p=S/'source-root/ShielddSecurity'/(n+'.lean');p.parent.mkdir(parents=True,exist_ok=True);require(len(t.encode())<=262144,'source budget')
with p.open('xb')as f:f.write(t.encode())
with(S/'generation01.json').open('x')as f:json.dump(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),data=pin(D),extractor=pin(S/'extract.py'),source=pin(p),audits=names),f,sort_keys=True)
print(json.dumps(dict(source=pin(p),audits=len(names))))
