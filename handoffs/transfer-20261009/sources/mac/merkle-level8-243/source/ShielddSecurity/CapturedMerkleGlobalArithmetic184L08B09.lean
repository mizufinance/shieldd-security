import ShielddSecurity.CapturedMerkleSparse243L08B09
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleSparse243L08B09.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 8).drop 144 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleSparse243L08B09.indices
def localParent : Nat → Option Row := CapturedMerkleSparse243L08B09.localParent
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [6682,6683,6684,6685,6686,6687,6688,6689,6690,6691,6692,6693,6694,6695,6696,6697] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl

def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleSparse243L08B09.local_checked
theorem count : rows.length=16 := CapturedMerkleSparse243L08B09.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.rows_exact
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.localParent
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.parent_equal
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L08B09.sound
