import ShielddSecurity.CapturedRegistrySparse244G24
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.RegistryWhole23
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGlobalBinding175G24
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedRegistrySparse244G24.rows
theorem rows_exact : rows=(RegistryWhole23.selectedRows.drop 384 |>.take 16) := by rfl
def indices : List Nat := CapturedRegistrySparse244G24.indices
def localParent : Nat → Option Row := CapturedRegistrySparse244G24.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [2690,2691,2692,2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedRegistrySparse244G24.local_checked
theorem count : rows.length=16 := CapturedRegistrySparse244G24.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedRegistryGlobalBinding175G24

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.rows
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.rows_exact
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.indices
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.localParent
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.parent_equal
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.productionCheck
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.checked
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.count
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.count
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G24.sound
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G24.sound
