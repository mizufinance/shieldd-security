import ShielddSecurity.CapturedMerkleFirstSparse245B21
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleHash27Whole
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstGlobal186B21
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleFirstSparse245B21.rows
theorem rows_exact : rows=(MerkleHash27Whole.selectedRows.drop 336 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleFirstSparse245B21.indices
def localParent : Nat → Option Row := CapturedMerkleFirstSparse245B21.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [3070,3071,3072,3073,3074,3075,3076,3077,3078,3079,3080,3081,3082,3083,3084,3085] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleFirstSparse245B21.local_checked
theorem count : rows.length=16 := CapturedMerkleFirstSparse245B21.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleFirstGlobal186B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.rows
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.rows_exact
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.indices
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.parent_equal
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.productionCheck
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.checked
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.count
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B21.sound
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B21.sound
