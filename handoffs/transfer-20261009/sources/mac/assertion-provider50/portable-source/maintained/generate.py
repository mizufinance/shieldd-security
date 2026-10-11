"""Immutable provider emission; exact original rows and assertion expression hints.

Hints describe source-reference LCs only. Source graph evaluation is separate.
"""
from pathlib import Path
import sys,json,zlib,hashlib,re,argparse
parser=argparse.ArgumentParser()
for key in ['output','qualification','extra','coefficients','data-directory','coefficient-source']:parser.add_argument('--'+key,required=True)
args=parser.parse_args()
S=Path(args.output)
LEGACY=set(range(25))|{76,89}

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
Q=Path(args.qualification);require(pin(Q)['sha256']=='76342258e7741b9f7863117c4784161329e4be86910bbf57388fcafa589cc9c6','exact qualification before DATA load')
q=strict(Q.read_bytes());extra=Path(args.extra);require(all(pin(extra)[k]==q['extra_coefficients'][k]for k in ['bytes','sha256']),'exact coefficient extension');e=strict(extra.read_bytes())
base=Path(args.coefficients);require(all(pin(base)[k]==q['old_coefficients'][k]for k in ['bytes','sha256'])and e['old_store']==q['old_coefficients'],'exact inherited coefficient store')
old=strict(base.read_bytes())['coefficients'];require(e['first_index']==len(old)==7483 and len(e['coefficients'])==13,'closed old/new coefficient domain')
ids={v:i for i,v in enumerate(old+e['coefficients'])};require(len(ids)==7496,'unique coefficient IDs')
root=S/'source-root/ShielddSecurity';root.mkdir(parents=True);outputs=[]
def audits(text,name):
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',text,re.M)
 existing=re.findall(r'^#check @ShielddSecurity\.'+name+r'\.(\w+)',text,re.M)
 return text+'\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'for n in names if n not in existing),['ShielddSecurity.'+name+'.'+n for n in names]
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
text,names=audits(text,'AssertionCoefficients50');p=Path(args.coefficient_source);require(p.read_bytes()==text.encode(),'exact qualified coefficient extension source; no replay')
for block in q['chunks']:
 data=Path(args.data_directory)/Path(block['data']['path']).name;require(all(pin(data)[k]==block['data'][k]for k in ['bytes','sha256']),'compressed DATA before decode')
 dec=zlib.decompressobj();raw=dec.decompress(data.read_bytes(),1048577);require(len(raw)<=1048576 and dec.eof and not dec.unused_data and not dec.unconsumed_tail,'bounded single complete zlib frame')
 require(len(raw)==block['decoded_bytes']and hashlib.sha256(raw).hexdigest()==block['decoded_sha256'],'decoded identity')
 d=strict(raw);require(d['start']==block['start']and len(d['records'])==d['count']==block['count'],'exact block shape')
 name='CapturedAssertions50B'+str(block['index']).zfill(4);terms=[];rows=[];hints=[]
 used=sorted({co for record in d['records'] for v in [*record['actual'],record.get('x',[]),record.get('y',[])] for _,co in v});require(used and all(type(co)is int and 0<=co<7496 for co in used),'closed exact local coefficient domain')
 coefficients=old+e['coefficients'];local_ids={co:i for i,co in enumerate(used)}
 def local_table(lo,hi):
  if hi-lo==1:return str(coefficients[used[lo]])
  m=(lo+hi)//2;return f'(if index<{m} then {local_table(lo,m)} else {local_table(m,hi)})'
 literal_coefficients=block['index']not in LEGACY
 local_definition=('\n'.join(f'private def c{i} : Int := {coefficients[co]}'for i,co in enumerate(used))if literal_coefficients else 'private noncomputable def localCoefficient (index : Nat) : Int := '+local_table(0,len(used)))

 def lc(v):
  index=len(terms);local=[(col,local_ids[co])for col,co in v];terms.append(local);literal='['+','.join(f'({col},c{co})'if literal_coefficients else f'({col},{co})'for col,co in local)+']';return literal if literal_coefficients else f'linear localCoefficient {literal}'
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
 chunks=[];defs=[];proofs=[]
 stride=4 if literal_coefficients else 16
 for lo in range(0,len(rows),stride):
  no=len(chunks);a=f'actual_c{no}';h=f'hints_c{no}';k=f'checked_c{no}'
  defs += [f'private noncomputable def {a} : List Row := [{",".join(rows[lo:lo+stride])}]',f'private noncomputable def {h} : List (Bool × CompilerAssertionBlock51.Recipe) := [{",".join(hints[lo:lo+stride])}]']
  proofs += [f'private theorem {k} : CompilerAssertionPairs55.checkPairs p copy {a} {h}=true := by decide +kernel']
  chunks.append((a,h,k))
 def composed(items):
  if len(items)==1:return items[0]
  m=len(items)//2;al,hl,kl=composed(items[:m]);ar,hr,kr=composed(items[m:]);no=len(defs);a=f'actual_g{no}';h=f'hints_g{no}';k=f'checked_g{no}'
  defs.extend([f'private noncomputable def {a} : List Row := {al}++{ar}',f'private noncomputable def {h} : List (Bool × CompilerAssertionBlock51.Recipe) := {hl}++{hr}'])
  proofs.append(f'private theorem {k} : CompilerAssertionPairs55.checkPairs p copy {a} {h}=true := by\n  change CompilerAssertionPairs55.checkPairs p copy ({al}++{ar}) ({hl}++{hr})=true\n  rw [CompilerAssertionPairs55.checkPairs_append p copy {al} {ar} {hl} {hr} (by rfl),{kl},{kr}]\n  rfl')
  return a,h,k
 a,h,k=composed(chunks)
 text=f'''import ShielddSecurity.CompilerAssertionPairs55
import ShielddSecurity.CompilerIndexedRecipe38
import ShielddSecurity.AssertionCoefficients50
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open CompilerIndexedRecipe38 CompilerAssertionBlock51 CompilerArithmeticTransport41
{local_definition}
noncomputable def terms (index : Nat) : Terms := {tree(0,len(terms))}
{chr(10).join(defs)}
noncomputable def actual : List Row := {a}
noncomputable def recipes : List (Bool × CompilerAssertionBlock51.Recipe) := {h}
theorem count_exact : actual.length={d['count']} := by rfl
'''
 for n in ['terms','actual','recipes','count_exact']:
  text+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 text+=chr(10).join(proofs)+f'''
theorem checked : CompilerAssertionPairs55.checkPairs p copy actual recipes=true := {k}
noncomputable def block : CompilerAssertionBlock51.Block p copy {d['count']} :=
  CompilerAssertionPairs55.leaf p copy {d['count']} actual recipes count_exact checked
theorem every_position (index : Nat) (bound : index<{d['count']}) : ∃ row,block.actual index=some row :=
  CompilerAssertionBlock51.every_position p copy {d['count']} block index bound
def captureIndex (index : Nat) := {d['start']}+index
theorem capture_position (index : Nat) (bound : index<{d['count']}) : captureIndex index<200770 := by
  change {d['start']}+index<200770
  omega
end ShielddSecurity.{name}
'''
 text,names=audits(text,name);require(len(text.encode())<=262144,'finite source cap')
 p=root/(name+'.lean');write(p,text.encode());outputs.append(dict(name=name,source=pin(p),audits=names,start=d['start'],count=d['count'],data=block['data'],local_coefficient_ids=used,local_coefficient_count=len(used),scope='Exact outlined rows and bidirectional expression-equality recipes; no original graph/evaluator or legal-input truth claim.'))
write(S/'generation01.json',(json.dumps(dict(generator=pin(Path(__file__)),qualification=pin(Q),outputs=outputs,total_source_bytes=sum(x['source']['bytes']for x in outputs),scope='SOURCE only; same checkRow Boolean with direct per-consumer encoded lists and exact per-block coefficient subset and16-row pair blocks; no legal-input truth claim; preserved both failed predecessor representations and receipts.'),sort_keys=True,separators=(',',':'))+'\n').encode())
print(json.dumps(dict(modules=len(outputs),source_bytes=sum(x['source']['bytes']for x in outputs),max_source=max(x['source']['bytes']for x in outputs))))
