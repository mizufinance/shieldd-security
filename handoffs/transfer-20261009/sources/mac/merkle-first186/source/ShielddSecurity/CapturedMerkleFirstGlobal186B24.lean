import ShielddSecurity.CapturedMerkleFirstSparse245B24
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleHash27Whole
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstGlobal186B24
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleFirstSparse245B24.rows
theorem rows_exact : rows=(MerkleHash27Whole.selectedRows.drop 384 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleFirstSparse245B24.indices
def localParent : Nat → Option Row := CapturedMerkleFirstSparse245B24.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [3118,3119,3120,3121,3122,3123,3124,3125,3126,3127,3128,3129,3130,3131,3132,3133] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleFirstSparse245B24.local_checked
theorem count : rows.length=16 := CapturedMerkleFirstSparse245B24.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleFirstGlobal186B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.rows
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.rows_exact
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.indices
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.parent_equal
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.productionCheck
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.checked
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.count
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B24.sound
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B24.sound
