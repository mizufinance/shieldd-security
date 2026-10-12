import ShielddSecurity.CapturedRegistrySparse244G25
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.RegistryWhole23
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGlobalBinding175G25
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedRegistrySparse244G25.rows
theorem rows_exact : rows=(RegistryWhole23.selectedRows.drop 400 |>.take 16) := by rfl
def indices : List Nat := CapturedRegistrySparse244G25.indices
def localParent : Nat → Option Row := CapturedRegistrySparse244G25.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [2706,2707,2708,2709,2710,2711,2712,2713,2714,2715,2716,2717,2718,2719,2720,2721] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedRegistrySparse244G25.local_checked
theorem count : rows.length=16 := CapturedRegistrySparse244G25.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedRegistryGlobalBinding175G25

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.rows
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.rows_exact
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.indices
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.localParent
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.parent_equal
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.productionCheck
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.checked
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.count
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.count
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G25.sound
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G25.sound
