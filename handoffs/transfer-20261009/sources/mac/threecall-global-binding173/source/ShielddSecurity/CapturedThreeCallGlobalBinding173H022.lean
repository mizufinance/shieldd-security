import ShielddSecurity.CompilerIndexedCopyConstant178
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.TransferPoseidonThreeCallJoin15Program01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedThreeCallGlobalBinding173H022
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := (TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 608).take 16
def indices : List Nat := List.range' 1342 16
noncomputable def productionCheck : Bool := CompilerIndexedCopyConstant178.check copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=16 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows :=
  CompilerIndexedCopyConstant178.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedThreeCallGlobalBinding173H022

set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173H022.rows
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173H022.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173H022.indices
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173H022.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173H022.productionCheck
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173H022.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173H022.checked
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173H022.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173H022.count
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173H022.count
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173H022.sound
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173H022.sound
