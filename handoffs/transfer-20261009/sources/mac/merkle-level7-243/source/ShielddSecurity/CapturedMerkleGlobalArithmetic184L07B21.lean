import ShielddSecurity.CapturedMerkleSparse243L07B21
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleSparse243L07B21.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 7).drop 336 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleSparse243L07B21.indices
def localParent : Nat → Option Row := CapturedMerkleSparse243L07B21.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [6450,6451,6452,6453,6454,6455,6456,6457,6458,6459,6460,6461,6462,6463,6464,6465] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleSparse243L07B21.local_checked
theorem count : rows.length=16 := CapturedMerkleSparse243L07B21.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.rows_exact
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.localParent
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.parent_equal
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L07B21.sound
