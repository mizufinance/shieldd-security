import ShielddSecurity.CompilerIndexedCopyConstant178
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.TransferPoseidonThreeCallJoin15Program01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedJoinPack179Pilot32
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := (TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 0).take 32
def indices : List Nat := List.range' 734 32
noncomputable def productionCheck : Bool := CompilerIndexedCopyConstant178.check copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=32 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows :=
  CompilerIndexedCopyConstant178.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedJoinPack179Pilot32

set_option pp.all true in
#check @ShielddSecurity.CapturedJoinPack179Pilot32.rows
#print axioms ShielddSecurity.CapturedJoinPack179Pilot32.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedJoinPack179Pilot32.indices
#print axioms ShielddSecurity.CapturedJoinPack179Pilot32.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedJoinPack179Pilot32.productionCheck
#print axioms ShielddSecurity.CapturedJoinPack179Pilot32.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedJoinPack179Pilot32.checked
#print axioms ShielddSecurity.CapturedJoinPack179Pilot32.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedJoinPack179Pilot32.count
#print axioms ShielddSecurity.CapturedJoinPack179Pilot32.count
set_option pp.all true in
#check @ShielddSecurity.CapturedJoinPack179Pilot32.sound
#print axioms ShielddSecurity.CapturedJoinPack179Pilot32.sound
