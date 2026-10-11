"""Balanced full arithmetic provider; no giant list or replay of completed leaves."""
from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent;R=S.parent.parent
def require(ok,reason):
 if not ok:raise ValueError(reason)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(p,b):
 with p.open('xb')as f:f.write(b)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source preparation')
require(not(S/'generation01.json').exists()and not(S/'source-root').exists(),'no sealed refresh')
G=R/'work/mac-full-arithmetic45-source01/generation01.json';Q=R/'work/mac-full-arithmetic45-source01/qualification01.json'
require(pin(Q)['sha256']=='8a0f562167797af1dec72f99c7de9b8a88a8f9902dfcb5d4fb2b1ef7ce75de30','qualified original body partition')
g=json.loads(G.read_bytes());q=json.loads(Q.read_bytes());records=g['outputs'];require(len(records)==599,'complete fixed leaf set')
cursor=0
for i,(record,chunk)in enumerate(zip(records,q['chunks'])):
 require(record['name']=='CapturedArithmetic45B'+str(i).zfill(4)and record['start']==chunk['start']==cursor and record['count']==chunk['count'],'exact leaf identity/order/position')
 require(record['low']==22738+cursor and record['high']==22738+cursor+record['count'],'exact source write interval')
 require(pin(Path(record['source']['path']))==record['source'],'immutable source bytes')
 cursor+=record['count']
require(cursor==177954,'exact all arithmetic positions')
root=S/'source-root/ShielddSecurity';root.mkdir(parents=True);outputs=[]
def emit(name,text):
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',text,re.M)
 text+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'for n in names)
 p=root/(name+'.lean');require(len(text.encode())<=262144,'finite source size');write(p,text.encode());outputs.append(dict(name=name,source=pin(p),audits=['ShielddSecurity.'+name+'.'+n for n in names]))
def tree(records):
 if len(records)==1:return records[0]['name']+'.block'
 mid=len(records)//2;left=records[:mid];right=records[mid:];lo=left[0]['low'];n=sum(x['count']for x in left);m=sum(x['count']for x in right)
 return f'(CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy {lo} {n} {m} {tree(left)} {tree(right)})'
groups=[]
for i in range(0,599,64):
 chunk=records[i:i+64];name='CapturedArithmetic52G'+str(len(groups)).zfill(2);low=chunk[0]['low'];count=sum(x['count']for x in chunk)
 text=''.join('import ShielddSecurity.'+r['name']+'\n'for r in chunk)+f'''import ShielddSecurity.CompilerArithmeticBlock44
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open CompilerArithmeticTransport41
noncomputable def block : CompilerArithmeticBlock44.Block ArithmeticCoefficients39.value copy {low} {count} := {tree(chunk)}
end ShielddSecurity.{name}
'''
 emit(name,text);groups.append(dict(name=name,low=low,count=count,start=chunk[0]['start']))
name='CapturedFullArithmetic52'
text=''.join('import ShielddSecurity.'+r['name']+'\n'for r in groups)+f'''import ShielddSecurity.CompilerArithmeticFixed48
import ShielddSecurity.CompilerArithmeticUniqueness49
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open CompilerArithmeticTransport41
noncomputable def block : CompilerArithmeticBlock44.Block ArithmeticCoefficients39.value copy 22738 177954 := {tree(groups)}
noncomputable def rowAt := block.actual
theorem every_position (index : Nat) (bound : index<177954) : ∃ row, rowAt index=some row :=
  CompilerArithmeticBlock44.every_position ArithmeticCoefficients39.value copy 22738 177954 block index bound
theorem exact_reverse (index : Nat) (row : Row) : rowAt index=some row ↔
    CompilerCachedArithmetic42.rowAt ArithmeticCoefficients39.value 22738 block.tree index=some row :=
  CompilerArithmeticBlock44.exact_reverse ArithmeticCoefficients39.value copy 22738 177954 block index row
variable {{F : Type}} [Field F] [CharP F p]
noncomputable def completed (base : Nat → F) :=
  CompilerArithmeticBlock44.completed ArithmeticCoefficients39.value copy 22738 177954 block base
theorem complete (base : Nat → F) : CompilerArithmeticBlock44.SatisfiesAt (completed base) rowAt 177954 :=
  CompilerArithmeticBlock44.complete ArithmeticCoefficients39.value copy 22738 177954 block base (by decide) (CompilerArithmeticTransport41.four_ne_zero (F:=F))
omit [CharP F p] in
theorem outside (base : Nat → F) (column : Nat) (bound : column<22738 ∨ 200692≤column) : completed base column=base column :=
  CompilerArithmeticBlock44.outside ArithmeticCoefficients39.value copy 22738 177954 block base column bound
omit [CharP F p] in
theorem original_inputs (base : Nat → F) (input : Nat) (bound : input<22735) : completed base (3+input)=base (3+input) :=
  CompilerArithmeticBlock44.inputs ArithmeticCoefficients39.value copy 177954 block base input bound
omit [CharP F p] in
theorem fixed (base : Nat → F) : completed base 0=base 0 ∧ completed base 1=base 1 ∧ completed base 2=base 2 ∧ completed base copy=base copy :=
  CompilerArithmeticBlock44.fixed ArithmeticCoefficients39.value copy 22738 177954 block base (by decide) (by decide)
theorem fixed_point (rho : Nat → F) (sat : CompilerArithmeticBlock44.SatisfiesAt rho rowAt 177954) : completed rho=rho :=
  CompilerArithmeticFixed48.block_fixed ArithmeticCoefficients39.value copy 22738 177954 block rho sat (CompilerArithmeticTransport41.four_ne_zero (F:=F))
theorem unique_completed (base rho : Nat → F)
    (agree : CompilerArithmeticUniqueness49.PrefixAgreement copy 22738 base rho)
    (sat : CompilerArithmeticBlock44.SatisfiesAt rho rowAt 177954) :
    CompilerArithmeticUniqueness49.PrefixAgreement copy 200692 (completed base) rho :=
  CompilerArithmeticUniqueness49.unique_completed ArithmeticCoefficients39.value copy 22738 177954 block base rho sat agree (CompilerArithmeticTransport41.four_ne_zero (F:=F))
theorem satisfying_unique (rho sigma : Nat → F)
    (agree : CompilerArithmeticUniqueness49.PrefixAgreement copy 22738 rho sigma)
    (left : CompilerArithmeticBlock44.SatisfiesAt rho rowAt 177954)
    (right : CompilerArithmeticBlock44.SatisfiesAt sigma rowAt 177954) :
    CompilerArithmeticUniqueness49.PrefixAgreement copy 200692 rho sigma := by
  have determined:=unique_completed rho sigma agree right
  rw [fixed_point rho left] at determined
  exact determined
end ShielddSecurity.{name}
'''
emit(name,text)
write(S/'generation01.json',(json.dumps(dict(generator=pin(Path(__file__)),full_leaf_generation=pin(G),qualified_data=pin(Q),inherited_leaf_sources=[x['source']for x in records],outputs=outputs,scope='SOURCE only until all inherited leaf objects/receipts and exact full root kernel executions qualify; covers arithmetic positions0..177953, not assertions or native Transfer.'),sort_keys=True,separators=(',',':'))+'\n').encode())
print(json.dumps(dict(modules=len(outputs),source_bytes=sum(x['source']['bytes']for x in outputs),root_audits=len(outputs[-1]['audits']))))
