import ShielddSecurity.CapturedMerkleSparse243L12B07
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleSparse243L12B07.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 12).drop 112 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleSparse243L12B07.indices
def localParent : Nat → Option Row := CapturedMerkleSparse243L12B07.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [8346,8347,8348,8349,8350,8351,8352,8353,8354,8355,8356,8357,8358,8359,8360,8361] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleSparse243L12B07.local_checked
theorem count : rows.length=16 := CapturedMerkleSparse243L12B07.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.rows_exact
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.localParent
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.parent_equal
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L12B07.sound
