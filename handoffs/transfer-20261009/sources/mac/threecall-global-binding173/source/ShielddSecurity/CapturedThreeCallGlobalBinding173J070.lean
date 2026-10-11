import ShielddSecurity.TransferPoseidonThreeCallJoin15Proof01
import ShielddSecurity.CompilerIndexedCopyConstant178
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.TransferPoseidonThreeCallJoin15Program01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedThreeCallGlobalBinding173J070
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := (TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 1296).take 8
def indices : List Nat := List.range' 2030 8
noncomputable def productionCheck : Bool := CompilerIndexedCopyConstant178.check copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=8 := by
  have total := TransferPoseidonThreeCallJoin15Proof01.row_count
  change (TransferPoseidonThreeCallJoin15Program01.arithmeticRows++[TransferPoseidonWidth3Call08Shared01.rawCopy]).length=1573 at total
  simp only [List.length_append,List.length_singleton] at total
  have size : TransferPoseidonThreeCallJoin15Program01.arithmeticRows.length=1572 := by omega
  change ((TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 1296).take 8).length=8
  rw [List.length_take,List.length_drop,size]
  rfl
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows :=
  CompilerIndexedCopyConstant178.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedThreeCallGlobalBinding173J070

set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173J070.rows
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173J070.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173J070.indices
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173J070.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173J070.productionCheck
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173J070.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173J070.checked
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173J070.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173J070.count
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173J070.count
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173J070.sound
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173J070.sound
