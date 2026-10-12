import ShielddSecurity.CapturedMerkleSparse243L13B23
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleSparse243L13B23.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 13).drop 368 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleSparse243L13B23.indices
def localParent : Nat → Option Row := CapturedMerkleSparse243L13B23.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [9026,9027,9028,9029,9030,9031,9032,9033,9034,9035,9036,9037,9038,9039,9040,9041] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleSparse243L13B23.local_checked
theorem count : rows.length=16 := CapturedMerkleSparse243L13B23.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.rows_exact
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.localParent
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.parent_equal
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23.sound
