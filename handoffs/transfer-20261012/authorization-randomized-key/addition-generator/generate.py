from pathlib import Path
import json,argparse,os,hashlib,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();tmp=a.output.with_name(a.output.name+'.pending');tmp.mkdir();dst=tmp/'source-root/ShielddSecurity';dst.mkdir(parents=True)
rows=json.loads((root/'rows.json').read_text())
def lc(ts):return '['+','.join(f'({c},{v})' for c,v in ts)+']'
def row(r):return '⟨'+lc(r[0])+','+lc(r[1])+'⟩'
name='CapturedAuthorizationAdd509';s='''-- GENERATED from rows.json by generate.py. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAuthorizationAdd509
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
'''
d='CapturedFirstSubgroup81.d';plus=f'[(copy,1),(64444,{d})]';minus=f'[(copy,1),(64444,-{d})]'
products=[('[(1980,1)]','[(4269,1)]'),('[(1981,1)]','[(4270,1)]'),('[(64440,1)]','[(64442,1)]'),(plus,minus),('[(4271,1)]','[(64446,1)]'),('[(1980,1)]','[(4270,1)]'),('[(1981,1)]','[(4269,1)]'),('[(64450,1),(64452,1)]',minus),('[(64454,1)]','[(4271,1)]'),('[(64440,1),(64442,1)]',plus),('[(64458,1)]','[(4271,1)]')]
expressions=['rho 1980*rho 4269','rho 1981*rho 4270','rho 64440*rho 64442',f'(1+({d}:F)*rho 64444)*(1-({d}:F)*rho 64444)','rho 4271*rho 64446','rho 1980*rho 4270','rho 1981*rho 4269',f'(rho 64450+rho 64452)*(1-({d}:F)*rho 64444)','rho 64454*rho 4271',f'(rho 64440+rho 64442)*(1+({d}:F)*rho 64444)','rho 64458*rho 4271']
for i,((left,right),expr) in enumerate(zip(products,expressions)):
 start=41702+2*i;out=22738+start
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
    let left := VariableWindowColumns449.columnPoint rho 1980
    let right := VariableWindowColumns449.columnPoint rho 4269
    let dt := Group.delta (CapturedFirstSubgroup81.d:F) left right
    rho 64448=rho 4271*((1+dt)*(1-dt)) ∧
    rho 64456=Group.cross left right*(1-dt)*rho 4271 ∧
    rho 64460=Group.diagonal left right*(1+dt)*rho 4271 := by
  dsimp only
'''
for i in reversed(range(11)):s+=f'  have v{i} := value{i} rho one arithmetic\n'
s+='  rw ['+','.join(f'v{i}' for i in reversed(range(11)))+']\n'
s+='  simp only [VariableWindowColumns449.columnPoint,Group.delta,Group.cross,Group.diagonal]\n  constructor\n  · congr 2 <;> ring\n  constructor <;> ring\n'
s=s.replace('import ShielddSecurity.VariableOperationAdapter434\n','import ShielddSecurity.VariableOperationAdapter434\nimport ShielddSecurity.VariableWindowColumns449\n')
s+='def positions : List Nat := [4280,4288,4289]\ndef actualRows : List Row := ['+','.join(row(rows[str(j)]) for j in [182234,182242,182243])+']\n'
s+='''def templates : List Row :=
  [⟨subtract [(copy,1)] [(64448,1)],[]⟩,⟨subtract [(64456,1)] [(4272,1)],[]⟩,⟨subtract [(64460,1)] [(4273,1)],[]⟩]
theorem actual_checked : (List.range 3).all (fun i => decide
    (CapturedFullRelation58.rowAt (177954+positions.getD i 0)=actualRows[i]?))=true := by decide +kernel
theorem forward_checked : VariableOperationAdapter434.covers templates actualRows=true := by decide +kernel
theorem reverse_checked : VariableOperationAdapter434.covers actualRows templates=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+positions.getD i 0)) 3

theorem rows_iff (rho : Nat → F) (one : rho copy=1) : Rows rho ↔
    rho 64448=1 ∧ rho 64456=rho 4272 ∧ rho 64460=rho 4273 := by
  have actual : Rows rho ↔ Satisfies rho actualRows := by
    constructor
    · intro sat row member
      obtain ⟨i,found⟩ := List.mem_iff_getElem?.mp member
      have bound : i<3 := (List.getElem?_eq_some_iff.mp found).1
      have check := of_decide_eq_true (List.all_eq_true.mp actual_checked i (List.mem_range.mpr bound))
      exact sat i bound row (check.trans found)
    · intro sat i bound row found
      have check := of_decide_eq_true (List.all_eq_true.mp actual_checked i (List.mem_range.mpr bound))
      exact sat row (List.mem_iff_getElem?.mpr ⟨i,check.symm.trans found⟩)
  rw [actual]
  have equivalent : Satisfies rho actualRows ↔ Satisfies rho templates :=
    ⟨transfer rho _ _ forward_checked,transfer rho _ _ reverse_checked⟩
  rw [equivalent]
  simp only [templates,Satisfies,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,VariableDoubleTemplate431.equality_row,eval,
    Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,←sub_eq_add_neg,sub_eq_zero]
  simp only [eq_comm]
end ShielddSecurity.CapturedAuthorizationAdd509
'''
for n in re.findall(r'^(?:def|theorem) (\w+)',s,re.M):s+='\nset_option pp.all true in\n#check @ShielddSecurity.'+name+'.'+n+'\n#print axioms ShielddSecurity.'+name+'.'+n+'\n'
p=dst/(name+'.lean');p.write_text(s);(tmp/'generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))+'\n');os.replace(tmp,a.output)
