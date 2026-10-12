import ShielddSecurity.CapturedMerkleFirstSparse245B18
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleHash27Whole
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstGlobal186B18
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleFirstSparse245B18.rows
theorem rows_exact : rows=(MerkleHash27Whole.selectedRows.drop 288 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleFirstSparse245B18.indices
def localParent : Nat → Option Row := CapturedMerkleFirstSparse245B18.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [3022,3023,3024,3025,3026,3027,3028,3029,3030,3031,3032,3033,3034,3035,3036,3037] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleFirstSparse245B18.local_checked
theorem count : rows.length=16 := CapturedMerkleFirstSparse245B18.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleFirstGlobal186B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.rows
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.rows_exact
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.indices
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.parent_equal
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.productionCheck
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.checked
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.count
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B18.sound
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B18.sound
