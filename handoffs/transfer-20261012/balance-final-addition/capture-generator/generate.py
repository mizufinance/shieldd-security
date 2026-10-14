from pathlib import Path
import json,argparse,os,hashlib,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();tmp=a.output.with_name(a.output.name+'.pending');tmp.mkdir();dst=tmp/'source-root/ShielddSecurity';dst.mkdir(parents=True)
rows=json.loads((root/'rows.json').read_text())
def lc(ts):return '['+','.join(f'({c},{v})' for c,v in ts)+']'
def row(r):return '⟨'+lc(r[0])+','+lc(r[1])+'⟩'
name='BalanceFinalAdd747';s='''-- GENERATED from rows.json by generate.py. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceFinalAdd747
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
'''
d='CapturedFirstSubgroup81.d';plus=f'[(copy,1),(195218,{d})]';minus=f'[(copy,1),(195218,-{d})]'
products=[('[(22230,1),(192706,1)]','[(22734,1)]'),('[(22231,1)]','[(22735,1)]'),('[(195214,1)]','[(195216,1)]'),(plus,minus),('[(22736,1)]','[(195220,1)]'),('[(22230,1),(192706,1)]','[(22735,1)]'),('[(22231,1)]','[(22734,1)]'),('[(195224,1),(195226,1)]',minus),('[(195228,1)]','[(22736,1)]'),('[(195214,1),(195216,1)]',plus),('[(195232,1)]','[(22736,1)]')]
expressions=['(rho 22230+rho 192706)*rho 22734','rho 22231*rho 22735','rho 195214*rho 195216',f'(1+({d}:F)*rho 195218)*(1-({d}:F)*rho 195218)','rho 22736*rho 195220','(rho 22230+rho 192706)*rho 22735','rho 22231*rho 22734',f'(rho 195224+rho 195226)*(1-({d}:F)*rho 195218)','rho 195228*rho 22736',f'(rho 195214+rho 195216)*(1+({d}:F)*rho 195218)','rho 195232*rho 22736']
for i,((left,right),expr) in enumerate(zip(products,expressions)):
 start=172476+2*i;out=22738+start
 s+=f'def rows{i} : List Row := ['+','.join(row(rows[str(j)]) for j in [start,start+1])+']\n'
 s+=f'''theorem actual{i} : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} 2 rows{i}=true := by decide +kernel
theorem checked{i} : (checkRow p rows{i} ⟨subtract {left} {right},[({out+1},1)]⟩ &&
  checkRow p rows{i} ⟨{left}++{right},[({out+1},1)]++scaleLinear 4 [({out},1)]⟩)=true := by decide +kernel
variable {{F : Type}} [Field F] [CharP F p] in
theorem value{i} (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho {out}={expr} := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 {start} 2 rows{i} actual{i} (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked{i}
  have result := checked_product_sound rho rows{i} {left} {right} [({out},1)] [({out+1},1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
'''
s+='''variable {F : Type} [Field F] [CharP F p]
theorem values (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    let left := Group.Point.mk (rho 22230+rho 192706) (rho 22231)
    let right := VariableWindowColumns449.columnPoint rho 22734
    let dt := Group.delta (CapturedFirstSubgroup81.d:F) left right
    rho 195222=rho 22736*((1+dt)*(1-dt)) ∧
    rho 195230=Group.cross left right*(1-dt)*rho 22736 ∧
    rho 195234=Group.diagonal left right*(1+dt)*rho 22736 := by
  dsimp only
'''
for i in reversed(range(11)):s+=f'  have v{i} := value{i} rho one arithmetic\n'
s+='  rw ['+','.join(f'v{i}' for i in reversed(range(11)))+']\n'
s+='  simp only [VariableWindowColumns449.columnPoint,Group.delta,Group.cross,Group.diagonal]\n  constructor\n  · congr 2 <;> ring\n  constructor <;> ring\n'
s=s.replace('import ShielddSecurity.VariableOperationAdapter434\n','import ShielddSecurity.VariableOperationAdapter434\nimport ShielddSecurity.VariableWindowColumns449\n')
s+='def signRows : List Row := ['+','.join(row(rows[str(j)]) for j in [169968,169969])+']\n'
s+='''theorem sign_actual : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 169968 2 signRows=true := by decide +kernel
theorem sign_checked : (checkRow p signRows ⟨subtract [(21711,1)] [(22230,-2)],[(192707,1)]⟩ &&
  checkRow p signRows ⟨[(21711,1)]++[(22230,-2)],[(192707,1)]++scaleLinear 4 [(192706,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem sign_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 192706=rho 21711*(-2*rho 22230) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 169968 2 signRows sign_actual (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp sign_checked
  have result := checked_product_sound rho signRows [(21711,1)] [(22230,-2)] [(192706,1)] [(192707,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_mul] using result
'''
s+='def assertionRows : List Row := ['+row(rows[str(177954+22811)])+']\n'
s+='theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+22811) 1 assertionRows=true := by decide +kernel\n\ntheorem rows (rho : Nat → F) (one : rho copy=1) (inverse : rho 195222=1) :\n    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22811+i)) 1 := by\n  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+22811) 1 assertionRows captured rho).mp\n  intro row member\n  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member\n  subst row\n  change eval rho [(195222,(p:Int)-1),(copy,1)]*eval rho [(195222,(p:Int)-1),(copy,1)]=eval rho []\n  have shape : canonical p [(195222,(p:Int)-1),(copy,1)]=canonical p [(195222,-1),(copy,1)] := by decide +kernel\n  rw [canonical_equal rho _ _ shape]\n  simp only [eval,Int.cast_neg,Int.cast_one,one_mul,neg_mul,one,inverse,add_zero,neg_add_cancel,mul_zero,zero_mul]\nend ShielddSecurity.BalanceFinalAdd747\n'
for n in re.findall(r'^(?:def|theorem) (\w+)',s,re.M):s+='\nset_option pp.all true in\n#check @ShielddSecurity.'+name+'.'+n+'\n#print axioms ShielddSecurity.'+name+'.'+n+'\n'
p=dst/(name+'.lean');p.write_text(s);(tmp/'generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))+'\n');os.replace(tmp,a.output)
