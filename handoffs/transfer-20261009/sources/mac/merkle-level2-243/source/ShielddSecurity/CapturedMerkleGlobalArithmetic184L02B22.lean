import ShielddSecurity.CapturedMerkleSparse243L02B22
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleSparse243L02B22.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 2).drop 352 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleSparse243L02B22.indices
def localParent : Nat → Option Row := CapturedMerkleSparse243L02B22.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [4346,4347,4348,4349,4350,4351,4352,4353,4354,4355,4356,4357,4358,4359,4360,4361] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleSparse243L02B22.local_checked
theorem count : rows.length=16 := CapturedMerkleSparse243L02B22.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.rows_exact
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.localParent
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.parent_equal
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22.sound
