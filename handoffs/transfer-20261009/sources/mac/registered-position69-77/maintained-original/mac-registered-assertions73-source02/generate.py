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
p=W/'mac-registered-audit70-data01/qualification01.json';require(pin(p)['sha256']=='ee64c753d8a42420995ec074542a2b33e2a7d2604c885b2cfee4a55652441009','exactdata')
d=json.loads(p.read_bytes());nodes={v['id']:v for v in d['nodes']};constants={v['id']:int(v['value'],16)for v in d['constants']}
def expr(ref):
 k,i=ref
 if k==0:return []if constants[i]==0 else[[0,constants[i]]]
 if k==1:return [[3+i,1]]
 require(k==2 and i in nodes,'closednode');return nodes[i]['terms']
def lc(terms):return '['+','.join('('+str(c)+','+str(v if v<=P//2 else v-P)+')'for c,v in terms)+']'
zero=[nodes[i]['terms']for i in [431,437,445,451,460,467,475,481,489,495]]
recipes=[]
for v in d['assertions']:
 ctor=v['certificate']['constructor'];require(ctor in ['linear','squareLinear'],'closedassertion')
 recipes.append('(true,.'+('square'if ctor=='squareLinear'else'linear')+' '+lc(expr(v['left']))+' '+lc(expr(v['right']))+')')
t='import ShielddSecurity.CapturedRegisteredAudit71\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.CapturedRegisteredAssertions73\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51\nvariable {F : Type} [Field F] [CharP F p]\ntheorem primitive_assertions (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)\n    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)\n    (primitive : CapturedRegisteredAudit70.Primitive rho)\n    (guards : CapturedRegisteredAudit71.Guards rho) :\n    SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35 := by\n  apply (satisfies_iff copy 35 CapturedRegisteredAudit70.block rho linked).mpr\n  intro index bound hint found\n'
t+='  rcases (show '+' ∨ '.join('index='+str(i)for i in range(35))+' by omega) with '+'|'.join('rfl'for _ in range(35))+'\n'
for index in range(35):
 pair=index//7;offset=index%7
 t+=f'  · change some {recipes[index]}=some hint at found\n    cases found\n'
 if offset<6:
  i=2*pair+offset//3;kind=offset%3;prod=6*pair+2*(offset//3);z=lc(zero[i]);hint=115+2*i;inv=hint+1;out=23000+2*prod
  t+=f'    have h:=primitive {i} (by decide)\n    change CompilerZeroTest65.Primitive (eval rho {z}) (rho {hint}) (rho {inv}) at h\n    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h\n'
  if kind==0:
   t+=f'    change Square (eval rho [({hint},1)]) (eval rho [({hint},1)])\n    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1\n'
  elif kind==1:
   t+=f'    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod} (by decide)\n    change rho {out}=eval rho {z}*eval rho [({inv},1)] at pa\n    simp only [eval,Int.cast_one,one_mul,add_zero] at pa\n    change eval rho [({out},1)]=eval rho [(0,1),({hint},-1)]\n    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]\n    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1\n'
  else:
   t+=f'    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod+1} (by decide)\n    change rho {out+2}=eval rho {z}*eval rho [({hint},1)] at pb\n    simp only [eval,Int.cast_one,one_mul,add_zero] at pb\n    change eval rho []=eval rho [({out+2},1)]\n    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm\n'
 else:
  prod=6*pair+4;out=23000+2*prod;hint=115+4*pair
  t+=f'    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod} (by decide)\n    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod+1} (by decide)\n    change rho {out}=eval rho [({hint},1)]*eval rho [({hint+2},1)] at b\n    change rho {out+2}=eval rho [(10,1)]*eval rho [({out},1)] at c\n    simp only [eval,Int.cast_one,one_mul,add_zero] at b c\n    change eval rho []=eval rho [({out+2},1)]\n    have g:=guards {pair} (by decide)\n    change rho 10*(rho {hint}*rho {hint+2})=0 at g\n    simpa only [eval,Int.cast_one,one_mul,add_zero] using (c.trans ((congrArg (fun value => rho 10*value) b).trans g)).symm\n'
t+='theorem registered_iff (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)\n    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic) :\n    SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35 ↔\n    CapturedRegisteredAudit70.Primitive rho ∧ CapturedRegisteredAudit71.Guards rho := by\n  constructor\n  · intro sat\n    exact ⟨CapturedRegisteredAudit71.actual_primitive rho zero linked arithmeticSat sat,\n      CapturedRegisteredAudit71.actual_guards rho linked arithmeticSat sat⟩\n  · rintro ⟨primitive,guards⟩\n    exact primitive_assertions rho zero linked arithmeticSat primitive guards\nend ShielddSecurity.CapturedRegisteredAssertions73\n'
names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==2,'exact2decls')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedRegisteredAssertions73.{n}\n#print axioms ShielddSecurity.CapturedRegisteredAssertions73.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedRegisteredAssertions73.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),data=pin(W/'mac-registered-audit70-data01/qualification01.json'),source=pin(p),audits=['ShielddSecurity.CapturedRegisteredAssertions73.'+n for n in names],scope='SOURCE UNRUN. Actual35 assertion equivalence to ten zero primitives and five regulated guards under actual60 arithmetic; reverse witness direction, no desired assertion truth premise. No subgroup/base assertion premise introduced; no full legal/native conclusion.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(pin(p)))
