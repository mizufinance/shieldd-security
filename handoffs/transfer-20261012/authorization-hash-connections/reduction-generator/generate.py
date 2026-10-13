from pathlib import Path
import json,sys
S=Path(__file__).resolve().parent;out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=False);root=out/'source-root/ShielddSecurity';root.mkdir(parents=True);rows=json.loads((S/'rows.json').read_text());lc=lambda ts:'['+','.join(f'({c},{v})'for c,v in ts)+']'
s='''import ShielddSecurity.AuthorizationHash530C55
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.IncomingReduction533
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
'''
s+='def actualRows : List Row := ['+','.join('⟨'+lc(a)+','+lc(b)+'⟩'for a,b in rows)+']\n'
s+='''def templates : List Row :=
  [⟨subtract [(1995,1),(1994,6554484396890773809930967563523245729705921265872317281365359162392183254199)] AuthorizationHash530C55.result,[]⟩]
theorem actual_checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt 180207 1 actualRows=true := by decide +kernel
theorem forward_checked : VariableOperationAdapter434.covers templates actualRows=true := by decide +kernel
theorem reverse_checked : VariableOperationAdapter434.covers actualRows templates=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def Rows (rho : Nat → F) := SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (180207+i)) 1
theorem rows_iff (rho : Nat → F) : Rows rho ↔
    rho 1995+(TransferCore.scalarOrder:F)*rho 1994=eval rho AuthorizationHash530C55.result := by
  have actual : Rows rho ↔ Satisfies rho actualRows :=
    (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 180207 1 actualRows actual_checked rho).symm
  rw [actual]
  have equivalent : Satisfies rho actualRows ↔ Satisfies rho templates :=
    ⟨transfer rho _ _ forward_checked,transfer rho _ _ reverse_checked⟩
  rw [equivalent]
  simp only [templates,Satisfies,List.mem_singleton,forall_eq,eval,VariableDoubleTemplate431.equality_row]
  simp only [eval,Int.cast_one,one_mul,add_zero]
  simp only [TransferCore.scalarOrder,Int.cast_ofNat,Nat.cast_ofNat]
end ShielddSecurity.IncomingReduction533
'''
for n in ['actual_checked','forward_checked','reverse_checked','Rows','rows_iff']:s+=f'set_option pp.all true in\n#check @ShielddSecurity.IncomingReduction533.{n}\n#print axioms ShielddSecurity.IncomingReduction533.{n}\n'
(root/'IncomingReduction533.lean').write_text(s)
print('Generated exact incoming reduction row')
