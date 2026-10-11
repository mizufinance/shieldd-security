from pathlib import Path
import json,hashlib,zlib,sys,re
S=Path(__file__).resolve().parent
def require(ok,reason):
 if not ok:raise ValueError(reason)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(b):
 def pairs(v):
  d={}
  for k,x in v:require(k not in d,'duplicate JSON key');d[k]=x
  return d
 return json.loads(b,object_pairs_hook=pairs)
def write(p,b):
 with p.open('xb')as f:f.write(b)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized interpreter')
require(not(S/'generation01.json').exists(),'immutable emission')
Q=S/'qualification01.json';require(pin(Q)['sha256']=='8a0f562167797af1dec72f99c7de9b8a88a8f9902dfcb5d4fb2b1ef7ce75de30','qualified complete arithmetic DATA')
q=strict(Q.read_bytes());c=Path(q['coefficient_store']['path']);require(pin(c)==q['coefficient_store'],'exact coefficient index')
(S/'source-root/ShielddSecurity').mkdir(parents=True);outputs=[]
for block in q['chunks']:
 p=Path(block['data']['path']);require(pin(p)==block['data'],'compressed DATA exact before decode')
 dec=zlib.decompressobj();raw=dec.decompress(p.read_bytes(),1048577);require(len(raw)<=1048576 and dec.eof and not dec.unused_data and not dec.unconsumed_tail,'bounded exact single zlib stream')
 require(len(raw)==block['decoded_bytes']and hashlib.sha256(raw).hexdigest()==block['decoded_sha256'],'decoded bytes pin')
 d=strict(raw);require(d['start']==block['start']and d['count']==block['count']and len(d['recipes'])==block['recipes'],'complete leaf shape')
 n='CapturedArithmetic45B'+str(block['index']).zfill(4);low=d['low'];count=d['count'];inputs=[];refs=[];rows=[];column=low
 for record in d['recipes']:
  node,width,*terms=record;require(width in [1,2]and len(terms)==width,'closed recipe')
  j=len(inputs);inputs+=terms
  if width==1:refs.append(f'.square (inputs {j})');rows.append(f'⟨linear ArithmeticCoefficients39.value (inputs {j}),[({column},1)]⟩')
  else:
   refs.append(f'.pair (inputs {j}) (inputs {j+1})');rows.append(f'⟨linear ArithmeticCoefficients39.value (inputs {j}),[({column+1},1)]⟩');rows.append(f'⟨linear ArithmeticCoefficients39.value (inputs {j+1}),[({column},4),({column+1},1)]⟩')
  column+=width
 require(column==low+count and len(inputs)==count,'every position emitted exactly')
 def encoded(ts):return '['+','.join(f'({col},{co})'for col,co in ts)+']'
 def balanced(lo,hi):
  if hi-lo==1:return encoded(inputs[lo])
  middle=(lo+hi)//2;return f'(if index<{middle} then {balanced(lo,middle)} else {balanced(middle,hi)})'
 text=f'''import ShielddSecurity.CompilerArithmeticBlock44
import ShielddSecurity.ArithmeticCoefficients39
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{n}
open CompilerIndexedRecipe38 CompilerArithmeticTransport41
noncomputable def inputs (index : Nat) : Terms := {balanced(0,len(inputs))}
noncomputable def recipes : List Recipe := [{','.join(refs)}]
noncomputable def actual : List Row := [{','.join(rows)}]
theorem span_exact : span recipes={count} := by decide +kernel
theorem support_checked : check copy {low} recipes=true := by decide +kernel
theorem rows_exact : CompilerFreshArithmetic35.rows {low} (decodeList ArithmeticCoefficients39.value recipes)=actual := by rfl
noncomputable def block : CompilerArithmeticBlock44.Block ArithmeticCoefficients39.value copy {low} {count} :=
  CompilerArithmeticBlock44.leaf ArithmeticCoefficients39.value copy {low} {count} recipes (fun index => actual[index]?) span_exact support_checked (fun index => by rw [rows_exact])
theorem every_position (index : Nat) (bound : index<{count}) : ∃ row : Row,block.actual index=some row :=
  CompilerArithmeticBlock44.every_position ArithmeticCoefficients39.value copy {low} {count} block index bound
noncomputable def captureIndex (index : Nat) := {d['start']}+index
theorem capture_position (index : Nat) (bound : index<{count}) : captureIndex index<177954 := by
  change {d['start']}+index<177954
  omega
end ShielddSecurity.{n}
'''
 names=re.findall(r'^\s*(?:noncomputable )?(?:def|theorem) (\w+)',text,re.M)
 text+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{n}.{x}\n#print axioms ShielddSecurity.{n}.{x}\n'for x in names)
 require(len(text.encode())<=262144,'bounded source')
 out=S/'source-root/ShielddSecurity'/(n+'.lean');write(out,text.encode());outputs.append(dict(name=n,source=pin(out),audits=['ShielddSecurity.'+n+'.'+x for x in names],data=block['data'],start=d['start'],count=count,low=low,high=low+count))
write(S/'generation01.json',(json.dumps(dict(generator=pin(Path(__file__)),qualification=pin(Q),outputs=outputs),sort_keys=True,separators=(',',':'))+'\n').encode())
print(json.dumps(dict(modules=len(outputs),source_bytes=sum(x['source']['bytes']for x in outputs),largest=max(x['source']['bytes']for x in outputs))))
