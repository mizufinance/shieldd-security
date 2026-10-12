import ShielddSecurity.CapturedMerkleSparse243L05B19
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleSparse243L05B19.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 5).drop 304 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleSparse243L05B19.indices
def localParent : Nat → Option Row := CapturedMerkleSparse243L05B19.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [5570,5571,5572,5573,5574,5575,5576,5577,5578,5579,5580,5581,5582,5583,5584,5585] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleSparse243L05B19.local_checked
theorem count : rows.length=16 := CapturedMerkleSparse243L05B19.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.rows_exact
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.localParent
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.parent_equal
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L05B19.sound
