from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def lin(ts):return '['+','.join(f'({c},{v})'for c,v in ts)+']'
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
D=S/'selected-data01.json';require(pin(D)['sha256']=='b3e4b3dfa258dc276f76314f9ae84f80c968bd7bd571b1cc745a93f1b11e239b','immutable DATA')
d=json.loads(D.read_bytes());n='CapturedArithmetic35Large';actual=[d['actual_outlined'][str(i)]for i in range(11032,11036)];cp=d['actual_outlined']['200769'];require(d['low']==33770 and d['count']==4 and len(d['recipes'])==2,'instance shape')
t='''import ShielddSecurity.CompilerFreshArithmetic35
import ShielddSecurity.CompilerIndexedCoverage36
import ShielddSecurity.MerkleBits29
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedArithmetic35Large
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
'''
t+='def arithmetic : Array Row := (Array.mk ['+','.join('⟨'+lin(x['a'])+','+lin(x['b'])+'⟩'for x in actual)+'])\n'
t+='def actualCopy : Row := ⟨'+lin(cp['a'])+','+lin(cp['b'])+'⟩\n'
refs=[]
for r in d['recipes']:
 j=r['relative'];refs.append('.square '+lin(actual[j]['a']) if r['kind']=='square'else '.pair '+lin(actual[j]['a'])+' '+lin(actual[j+1]['a']))
t+='def recipes : List CompilerFreshArithmetic35.Recipe := ['+','.join(refs)+']\n'
t+=(S/'template.lean').read_text()
t=t.replace('theorem checked : CompilerFreshArithmetic35.check copy 33770 recipes=true := by decide +kernel\n','theorem checked : CompilerFreshArithmetic35.check copy 33770 recipes=true := by decide +kernel\nset_option pp.all true in\n#check @ShielddSecurity.CapturedArithmetic35Large.checked\n#print axioms ShielddSecurity.CapturedArithmetic35Large.checked\n')
t=t.replace('theorem rows_exact : CompilerFreshArithmetic35.rows 33770 recipes=arithmetic.toList := by rfl\n','theorem rows_exact : CompilerFreshArithmetic35.rows 33770 recipes=arithmetic.toList := by rfl\nset_option pp.all true in\n#check @ShielddSecurity.CapturedArithmetic35Large.rows_exact\n#print axioms ShielddSecurity.CapturedArithmetic35Large.rows_exact\n')
names=re.findall(r'^\s*(?:def|theorem) ([\w.]+)',t,re.M);t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{n}.{x}\n#print axioms ShielddSecurity.{n}.{x}\n'for x in names if x not in ('checked','rows_exact'))
p=S/'source-root/ShielddSecurity'/(n+'.lean');p.parent.mkdir(parents=True,exist_ok=True);require(len(t.encode())<=262144,'source budget')
with p.open('xb')as f:f.write(t.encode())
with(S/'generation01.json').open('x')as f:json.dump(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),data=pin(D),extractor=pin(S/'extract.py'),source=pin(p),audits=names),f,sort_keys=True)
print(json.dumps(dict(source=pin(p),audits=len(names))))
