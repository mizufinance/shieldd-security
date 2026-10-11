import ShielddSecurity.CompilerIndexedCopyConstant178
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.TransferPoseidonThreeCallJoin15Program01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedThreeCallGlobalBinding173D007
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := (TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 256).take 32
def indices : List Nat := List.range' 990 32
noncomputable def firstRows : List Row := (TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 256).take 16
noncomputable def lastRows : List Row := (TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 272).take 16
noncomputable def firstCheck : Bool := CompilerIndexedCopyConstant178.check copy
  CapturedFullRelation58.rowAt 200770 (List.range' 990 16) firstRows
noncomputable def lastCheck : Bool := CompilerIndexedCopyConstant178.check copy
  CapturedFullRelation58.rowAt 200770 (List.range' 1006 16) lastRows
theorem first_checked : firstCheck=true := by decide +kernel
theorem last_checked : lastCheck=true := by decide +kernel
noncomputable def productionCheck : Bool := firstCheck && lastCheck
theorem checked : productionCheck=true := Bool.and_eq_true_iff.mpr ⟨first_checked,last_checked⟩
theorem partition : rows=firstRows++lastRows := by
  change (TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop 256).take (16+16)=_
  rw [List.take_add,List.drop_drop]
  rfl
theorem count : rows.length=32 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows := by
  have linked := (CapturedFullRelation58.verifier_links rho satisfied).2.2
  have first := CompilerIndexedCopyConstant178.sound copy CapturedFullRelation58.rowAt 200770
    (List.range' 990 16) firstRows first_checked rho linked satisfied
  have last := CompilerIndexedCopyConstant178.sound copy CapturedFullRelation58.rowAt 200770
    (List.range' 1006 16) lastRows last_checked rho linked satisfied
  rw [partition]
  intro row member
  rcases List.mem_append.mp member with member|member
  · exact first row member
  · exact last row member

end ShielddSecurity.CapturedThreeCallGlobalBinding173D007

set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.rows
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.indices
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.firstRows
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.firstRows
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.lastRows
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.lastRows
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.firstCheck
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.firstCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.lastCheck
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.lastCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.first_checked
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.first_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.last_checked
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.last_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.productionCheck
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.checked
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.partition
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.count
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.count
set_option pp.all true in
#check @ShielddSecurity.CapturedThreeCallGlobalBinding173D007.sound
#print axioms ShielddSecurity.CapturedThreeCallGlobalBinding173D007.sound
