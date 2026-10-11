"""Immutable provider emission; exact original rows and assertion expression hints.

Hints describe source-reference LCs only. Source graph evaluation is separate.
"""
from pathlib import Path
import sys,json,zlib,hashlib,re
S=Path(__file__).resolve().parent
def require(ok,reason):
 if not ok:raise ValueError(reason)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(data):
 def pairs(items):
  out={}
  for k,v in items:require(k not in out,'duplicate JSON key');out[k]=v
  return out
 return json.loads(data,object_pairs_hook=pairs)
def write(p,b):
 with p.open('xb')as f:f.write(b)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized flags')
require(not(S/'generation01.json').exists()and not(S/'source-root').exists(),'immutable source emission')
Q=S/'qualification01.json';require(pin(Q)['sha256']=='76342258e7741b9f7863117c4784161329e4be86910bbf57388fcafa589cc9c6','exact qualification before DATA load')
q=strict(Q.read_bytes());extra=Path(q['extra_coefficients']['path']);require(pin(extra)==q['extra_coefficients'],'exact coefficient extension');e=strict(extra.read_bytes())
base=Path(q['old_coefficients']['path']);require(pin(base)==q['old_coefficients']and e['old_store']==q['old_coefficients'],'exact inherited coefficient store')
old=strict(base.read_bytes())['coefficients'];require(e['first_index']==len(old)==7483 and len(e['coefficients'])==13,'closed old/new coefficient domain')
ids={v:i for i,v in enumerate(old+e['coefficients'])};require(len(ids)==7496,'unique coefficient IDs')
root=S/'source-root/ShielddSecurity';root.mkdir(parents=True);outputs=[]
def audits(text,name):
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',text,re.M)
 return text+'\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'for n in names),['ShielddSecurity.'+name+'.'+n for n in names]
values=e['coefficients']
def table(lo,hi):
 if hi-lo==1:return str(values[lo])
 m=(lo+hi)//2;return f'(if index<{m+7483} then {table(lo,m)} else {table(m,hi)})'
text=f'''import ShielddSecurity.ArithmeticCoefficients39
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AssertionCoefficients50
noncomputable def value (index : Nat) : Int := if index<7483 then ArithmeticCoefficients39.value index else {table(0,13)}
end ShielddSecurity.AssertionCoefficients50
'''
text,names=audits(text,'AssertionCoefficients50');p=root/'AssertionCoefficients50.lean';write(p,text.encode());outputs.append(dict(name=p.stem,source=pin(p),audits=names,scope='Inherited coefficient lookup plus thirteen literal values; DATA parity remains separately pinned.'))
for block in q['chunks']:
 data=Path(block['data']['path']);require(pin(data)==block['data'],'compressed DATA before decode')
 dec=zlib.decompressobj();raw=dec.decompress(data.read_bytes(),1048577);require(len(raw)<=1048576 and dec.eof and not dec.unused_data and not dec.unconsumed_tail,'bounded single complete zlib frame')
 require(len(raw)==block['decoded_bytes']and hashlib.sha256(raw).hexdigest()==block['decoded_sha256'],'decoded identity')
 d=strict(raw);require(d['start']==block['start']and len(d['records'])==d['count']==block['count'],'exact block shape')
 name='CapturedAssertions50B'+str(block['index']).zfill(4);terms=[];rows=[];hints=[]
 def lc(v):
  index=len(terms);terms.append(v);return f'linear AssertionCoefficients50.value (terms {index})'
 for j,record in enumerate(d['records']):
  require(record['index']==d['start']+j,'each position exact')
  a,b=record['actual'];rows.append(f'⟨{lc(a)},{lc(b)}⟩')
  if 'assertion'in record:
   require(record['assertion']==record['index']-177954 and record['constructor']in ['linear','squareLinear'],'exact assertion index/type')
   ctor='linear'if record['constructor']=='linear'else'square';hints.append(f'(true,.{ctor} ({lc(record["x"])}) ({lc(record["y"])}))')
  else:
   pair={200767:(1,22737),200768:(2,9),200769:(0,200692)}[record['index']]
   hints.append(f'(false,.linear [({pair[0]},1)] [({pair[1]},1)])')
 def encoded(v):return '['+','.join(f'({col},{co})'for col,co in v)+']'
 def tree(lo,hi):
  if hi-lo==1:return encoded(terms[lo])
  m=(lo+hi)//2;return f'(if index<{m} then {tree(lo,m)} else {tree(m,hi)})'
 text=f'''import ShielddSecurity.CompilerAssertionBlock51
import ShielddSecurity.CompilerIndexedRecipe38
import ShielddSecurity.AssertionCoefficients50
import ShielddSecurity.TransferPoseidonFirstSubgroupData01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open CompilerIndexedRecipe38 CompilerAssertionBlock51
noncomputable def terms (index : Nat) : Terms := {tree(0,len(terms))}
noncomputable def actual : List Row := [{','.join(rows)}]
noncomputable def recipes : List (Bool × CompilerAssertionBlock51.Recipe) := [{','.join(hints)}]
theorem count_exact : actual.length={d['count']} := by rfl
theorem checked : CompilerAssertionBlock51.checkList p copy actual recipes=true := by decide +kernel
noncomputable def block : CompilerAssertionBlock51.Block p copy {d['count']} :=
  CompilerAssertionBlock51.leaf p copy {d['count']} actual recipes count_exact checked
theorem every_position (index : Nat) (bound : index<{d['count']}) : ∃ row,block.actual index=some row :=
  CompilerAssertionBlock51.every_position p copy {d['count']} block index bound
def captureIndex (index : Nat) := {d['start']}+index
theorem capture_position (index : Nat) (bound : index<{d['count']}) : captureIndex index<200770 := by
  change {d['start']}+index<200770
  omega
end ShielddSecurity.{name}
'''
 # Exact owned shared constants module, not a heavy concrete semantic instance.
 text=text.replace('import ShielddSecurity.TransferPoseidonFirstSubgroupData01','import ShielddSecurity.CompilerArithmeticTransport41').replace('open CompilerIndexedRecipe38 CompilerAssertionBlock51','open CompilerIndexedRecipe38 CompilerAssertionBlock51 CompilerArithmeticTransport41')
 text,names=audits(text,name);require(len(text.encode())<=262144,'finite source cap')
 p=root/(name+'.lean');write(p,text.encode());outputs.append(dict(name=name,source=pin(p),audits=names,start=d['start'],count=d['count'],data=block['data'],scope='Exact outlined rows and bidirectional expression-equality recipes; no original graph/evaluator or legal-input truth claim.'))
write(S/'generation01.json',(json.dumps(dict(generator=pin(Path(__file__)),qualification=pin(Q),outputs=outputs,total_source_bytes=sum(x['source']['bytes']for x in outputs),scope='SOURCE only until exact kernel receipts; all source-reference/operation parity is DATA only'),sort_keys=True,separators=(',',':'))+'\n').encode())
print(json.dumps(dict(modules=len(outputs),source_bytes=sum(x['source']['bytes']for x in outputs),max_source=max(x['source']['bytes']for x in outputs))))
