from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def lin(ts):return '['+','.join(f'({c},{v})'for c,v in ts)+']'
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
D=S/'selected-data01.json';require(pin(D)['sha256']=='f083e4d9f766b87d5fee211b7870edc38e3fa7c15540d05bf93ff7e2622fa238','immutable DATA')
d=json.loads(D.read_bytes());n='CapturedArithmetic35Pilot';actual=[d['actual_outlined'][str(i)]for i in range(128)];cp=d['actual_outlined']['200769'];require(d['low']==22738 and d['count']==128 and len(d['recipes'])==72,'instance shape')
t='''import ShielddSecurity.CompilerFreshArithmetic35
import ShielddSecurity.CompilerIndexedCoverage36
import ShielddSecurity.MerkleBits29
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedArithmetic35Pilot
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
t=t.replace('theorem checked : CompilerFreshArithmetic35.check copy 22738 recipes=true := by decide +kernel\n','theorem checked : CompilerFreshArithmetic35.check copy 22738 recipes=true := by decide +kernel\nset_option pp.all true in\n#check @ShielddSecurity.CapturedArithmetic35Pilot.checked\n#print axioms ShielddSecurity.CapturedArithmetic35Pilot.checked\n')
t=t.replace('theorem rows_exact : CompilerFreshArithmetic35.rows 22738 recipes=arithmetic.toList := by rfl\n','theorem rows_exact : CompilerFreshArithmetic35.rows 22738 recipes=arithmetic.toList := by rfl\nset_option pp.all true in\n#check @ShielddSecurity.CapturedArithmetic35Pilot.rows_exact\n#print axioms ShielddSecurity.CapturedArithmetic35Pilot.rows_exact\n')
names=re.findall(r'^\s*(?:def|theorem) ([\w.]+)',t,re.M);t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{n}.{x}\n#print axioms ShielddSecurity.{n}.{x}\n'for x in names if x not in ('checked','rows_exact'))
p=S/'source-root/ShielddSecurity'/(n+'.lean');p.parent.mkdir(parents=True,exist_ok=True);require(len(t.encode())<=262144,'source budget')
with p.open('xb')as f:f.write(t.encode())
with(S/'generation01.json').open('x')as f:json.dump(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),data=pin(D),extractor=pin(S/'extract.py'),source=pin(p),audits=names),f,sort_keys=True)
print(json.dumps(dict(source=pin(p),audits=len(names))))
