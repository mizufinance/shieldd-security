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
t='import ShielddSecurity.CapturedRegisteredAudit70\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.CapturedRegisteredAudit71\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51\nvariable {F : Type} [Field F] [CharP F p]\ntheorem actual_primitive (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)\n    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)\n    (assertionsSat : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35) :\n    CapturedRegisteredAudit70.Primitive rho := by\n  have truth:=(satisfies_iff copy 35 CapturedRegisteredAudit70.block rho linked).mp assertionsSat\n  intro index bound\n'
t+='  rcases (show '+' ∨ '.join('index='+str(i)for i in range(10))+' by omega) with '+'|'.join('rfl'for _ in range(10))+'\n'
for i in range(10):
 pair=i//2;pos=7*pair+3*(i%2);prod=6*pair+2*(i%2);hint=115+2*i;inv=hint+1;out=23000+2*prod;z=lc(zero[i])
 t+=f'  · have a:=truth {pos} (by decide) {recipes[pos]} rfl\n    have b:=truth {pos+1} (by decide) {recipes[pos+1]} rfl\n    have c:=truth {pos+2} (by decide) {recipes[pos+2]} rfl\n'
 t+=f'    change Square (eval rho [({hint},1)]) (eval rho [({hint},1)]) at a\n    change eval rho [({out},1)]=eval rho [(0,1),({hint},-1)] at b\n    change eval rho []=eval rho [({out+2},1)] at c\n'
 t+='    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c\n    have bPrime : rho '+str(out)+'=1-rho '+str(hint)+' := by simpa only [zero,sub_eq_add_neg] using b\n'
 t+=f'    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod} (by decide)\n    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod+1} (by decide)\n'
 t+=f'    change rho {out}=eval rho {z}*eval rho [({inv},1)] at pa\n    change rho {out+2}=eval rho {z}*eval rho [({hint},1)] at pb\n    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb\n    change CompilerZeroTest65.Primitive (eval rho {z}) (rho {hint}) (rho {inv})\n    refine ⟨a,?_,?_⟩\n    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime\n    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm\n'
t+='def Guards (rho : Nat → F) : Prop := ∀ pair<5,\n  rho 10*(rho (115+4*pair)*rho (117+4*pair))=0\ntheorem actual_guards (rho : Nat → F) (linked : rho copy=rho 0)\n    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)\n    (assertionsSat : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35) : Guards rho := by\n  have truth:=(satisfies_iff copy 35 CapturedRegisteredAudit70.block rho linked).mp assertionsSat\n  intro pair bound\n  rcases (show pair=0 ∨ pair=1 ∨ pair=2 ∨ pair=3 ∨ pair=4 by omega) with rfl|rfl|rfl|rfl|rfl\n'
for pair in range(5):
 pos=7*pair+6;prod=6*pair+4;out=23000+2*prod;hint=115+4*pair
 t+=f'  · have a:=truth {pos} (by decide) {recipes[pos]} rfl\n    change eval rho []=eval rho [({out+2},1)] at a\n    simp only [eval,Int.cast_one,one_mul,add_zero] at a\n'
 t+=f'    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod} (by decide)\n    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat {prod+1} (by decide)\n    change rho {out}=eval rho [({hint},1)]*eval rho [({hint+2},1)] at b\n    change rho {out+2}=eval rho [(10,1)]*eval rho [({out},1)] at c\n    simp only [eval,Int.cast_one,one_mul,add_zero] at b c\n    change rho 10*(rho {hint}*rho {hint+2})=0\n    exact (congrArg (fun value => rho 10*value) b).symm.trans (c.symm.trans a.symm)\n'
t+='theorem forbidden_pair (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)\n    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)\n    (assertionsSat : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35)\n    (pair : Nat) (bound : pair<5) :\n    eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair))=0 ∧\n    eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair+1))=0 → rho 10=0 := by\n  have primitive:=actual_primitive rho zero linked arithmeticSat assertionsSat\n  have guards:=actual_guards rho linked arithmeticSat assertionsSat\n  have left:=primitive (2*pair) (by omega)\n  have right:=primitive (2*pair+1) (by omega)\n  have checked:=CompilerCoordinateZero69.guard_iff\n    (eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair)))\n    (eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair+1)))\n    (rho (115+2*(2*pair))) (rho (116+2*(2*pair)))\n    (rho (115+2*(2*pair+1))) (rho (116+2*(2*pair+1))) (rho 10) ⟨left,right⟩\n  apply checked.mp\n  have leftIndex : 115+2*(2*pair)=115+4*pair := by omega\n  have rightIndex : 115+2*(2*pair+1)=117+4*pair := by omega\n  simpa only [leftIndex,rightIndex] using guards pair bound\nend ShielddSecurity.CapturedRegisteredAudit71\n'
names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==4,'exact4decls')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedRegisteredAudit71.{n}\n#print axioms ShielddSecurity.CapturedRegisteredAudit71.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedRegisteredAudit71.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),data=pin(W/'mac-registered-audit70-data01/qualification01.json'),source=pin(p),audits=['ShielddSecurity.CapturedRegisteredAudit71.'+n for n in names],scope='SOURCE UNRUN. Actual35 assertions +60 arithmetic derives10 zero primitives and5 regulated pair-exclusion guards. No subgroup/base assertion premise introduced; no full legal/native conclusion.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(pin(p)))
