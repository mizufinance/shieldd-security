from pathlib import Path
import json,hashlib,re,sys
S=Path(__file__).resolve().parent;W=S.parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def require(v,msg):
 if not v:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists(),'no sealed refresh')
p=W/'mac-registered-audit70-data01/qualification01.json';require(pin(p)['sha256']=='ee64c753d8a42420995ec074542a2b33e2a7d2604c885b2cfee4a55652441009','exact frozen data')
d=json.loads(p.read_bytes());nodes={v['id']:v for v in d['nodes']};const={v['id']:int(v['value'],16)for v in d['constants']}
def expr(ref):
 k,i=ref
 if k==0:return []if const[i]==0 else[[0,const[i]]]
 if k==1:return [[3+i,1]]
 require(k==2 and i in nodes,'closed node reference');return nodes[i]['terms']
def lc(terms):return '['+','.join('('+str(c)+','+str(v if v<=P//2 else v-P)+')'for c,v in terms)+']'
products=[v for v in d['nodes']if v['certificate']['constructor']=='product'];require(len(products)==30,'actual30products')
for index,v in enumerate(products):require(v['op']=='mul'and v['certificate']['left']==v['left']and v['certificate']['right']==v['right']and v['terms']==[[23000+2*index,1]]and v['certificate']['rows']==[262+2*index,263+2*index],'raw constructor/position agreement')
left=[expr(v['left'])for v in products];right=[expr(v['right'])for v in products]
zero=[nodes[i]['terms']for i in [431,437,445,451,460,467,475,481,489,495]]
recipes=[]
for v in d['assertions']:
 ctor=v['certificate']['constructor'];require(ctor in ['linear','squareLinear'],'closed assertion constructor')
 recipes.append('(true,.'+('square'if ctor=='squareLinear'else'linear')+' '+lc(expr(v['left']))+' '+lc(expr(v['right']))+')')
t='import ShielddSecurity.CapturedArithmetic45B0000\nimport ShielddSecurity.CapturedAssertions50B0000\nimport ShielddSecurity.CompilerIndexed01\nimport ShielddSecurity.CompilerCoordinateZero69\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.CapturedRegisteredAudit70\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51\nnoncomputable def arithmetic : List Row := (CapturedArithmetic45B0000.actual.drop 262).take 60\n'
t+='def productLeft (index : Nat) : Linear := ('+'['+','.join(lc(x)for x in left)+']'+').getD index []\n'
t+='def productRight (index : Nat) : Linear := ('+'['+','.join(lc(x)for x in right)+']'+').getD index []\n'
t+='def zeroTerms (index : Nat) : Linear := ('+'['+','.join(lc(x)for x in zero)+']'+').getD index []\n'
t+='noncomputable def productCheck : Bool := (List.range 30).all (fun index =>\n  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index)\n    ⟨subtract (productLeft index) (productRight index),[(23001+2*index,1)]⟩ &&\n  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index+1)\n    ⟨productLeft index++productRight index,[(23001+2*index,1)]++scaleLinear 4 [(23000+2*index,1)]⟩)\ntheorem products_checked : productCheck=true := by decide +kernel\nnoncomputable def assertions : List Row := (CapturedAssertions50B0000.actual.drop 94).take 35\n'
t+='def recipes : List (Bool × Recipe) := ['+','.join(recipes)+']\n'
t+='theorem assertions_checked : checkList p copy assertions recipes=true := by decide +kernel\nnoncomputable def block : Block p copy 35 := leaf p copy 35 assertions recipes (by decide +kernel) assertions_checked\nvariable {F : Type} [Field F]\ndef Primitive (rho : Nat → F) : Prop := ∀ index<10,\n  CompilerZeroTest65.Primitive (eval rho (zeroTerms index)) (rho (115+2*index)) (rho (116+2*index))\nvariable [CharP F p]\ntheorem product_value (rho : Nat → F) (linked : rho copy=rho 0)\n    (satisfied : Satisfies rho arithmetic) (index : Nat) (bound : index<30) :\n    rho (23000+2*index)=eval rho (productLeft index)*eval rho (productRight index) := by\n  have checks:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp products_checked index (List.mem_range.mpr bound))\n  have rows : Satisfies rho (unoutlineRows copy arithmetic) := by\n    intro row member\n    obtain ⟨original,included,rfl⟩:=List.mem_map.mp member\n    simpa only [eval_unoutline rho copy _ linked] using satisfied original included\n  have minus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index)\n    ⟨subtract (productLeft index) (productRight index),[(23001+2*index,1)]⟩ checks.1\n  have plus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index+1)\n    ⟨productLeft index++productRight index,[(23001+2*index,1)]++scaleLinear 4 [(23000+2*index,1)]⟩ checks.2\n  have h:=checked_product_sound rho (unoutlineRows copy arithmetic) (productLeft index) (productRight index)\n    [(23000+2*index,1)] [(23001+2*index,1)] four_ne_zero rows\n    (by simpa only [List.toList_toArray] using minus) (by simpa only [List.toList_toArray] using plus)\n  simpa only [eval,Int.cast_one,one_mul,add_zero] using h\n'
names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==11,'exact11decls')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedRegisteredAudit70.{n}\n#print axioms ShielddSecurity.CapturedRegisteredAudit70.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedRegisteredAudit70.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),data=pin(W/'mac-registered-audit70-data01/qualification01.json'),source=pin(p),audits=['ShielddSecurity.CapturedRegisteredAudit70.'+n for n in names],scope='SOURCE UNRUN. Exact thirty actual product pairs and35 assertion syntax/coverage; product_value semantics. Primitive definition alone has no assertion truth credit. Full legal/native OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(pin(p)))
