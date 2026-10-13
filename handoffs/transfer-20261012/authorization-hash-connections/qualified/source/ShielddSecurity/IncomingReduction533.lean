import ShielddSecurity.AuthorizationHash530C55
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.IncomingReduction533
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def actualRows : List Row := [⟨[(1994,6554484396890773809930967563523245729705921265872317281365359162392183254199),(1995,1),(50178,46855940266913453502209730394455508830783759657335420049550374818274958592832),(50182,1456928232331769666091604024043650394538239072306372778700000267793573709090),(50186,698131897170581497048307930565348753692375937666850051123327179522779327497),(50190,52155120632190118924124156561149583535786380164772322260000241192699256431877),(50194,7662113046484220376376826760560917990503811480570254258903603224694465574129),(50198,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[]⟩]
def templates : List Row :=
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
set_option pp.all true in
#check @ShielddSecurity.IncomingReduction533.actual_checked
#print axioms ShielddSecurity.IncomingReduction533.actual_checked
set_option pp.all true in
#check @ShielddSecurity.IncomingReduction533.forward_checked
#print axioms ShielddSecurity.IncomingReduction533.forward_checked
set_option pp.all true in
#check @ShielddSecurity.IncomingReduction533.reverse_checked
#print axioms ShielddSecurity.IncomingReduction533.reverse_checked
set_option pp.all true in
#check @ShielddSecurity.IncomingReduction533.Rows
#print axioms ShielddSecurity.IncomingReduction533.Rows
set_option pp.all true in
#check @ShielddSecurity.IncomingReduction533.rows_iff
#print axioms ShielddSecurity.IncomingReduction533.rows_iff
