import ShielddSecurity.CapturedMerkleSparse243L04B04
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleSparse243L04B04.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 4).drop 64 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleSparse243L04B04.indices
def localParent : Nat → Option Row := CapturedMerkleSparse243L04B04.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [4906,4907,4908,4909,4910,4911,4912,4913,4914,4915,4916,4917,4918,4919,4920,4921] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleSparse243L04B04.local_checked
theorem count : rows.length=16 := CapturedMerkleSparse243L04B04.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.rows_exact
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.localParent
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.parent_equal
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04.sound
