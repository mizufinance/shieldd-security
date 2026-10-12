import ShielddSecurity.CapturedMerklePathGlobal187
import ShielddSecurity.CapturedMerkleBitsGlobal188
import ShielddSecurity.MerkleOrdered34
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleOrderedGlobal189
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem bit_encoding (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ bits : Fin 32 → Bool,∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i) :=
 MerkleOrdered34.exists_bits rho (CapturedMerkleBitsGlobal188.rows_sound rho satisfied)
theorem ordered_anchor (rho : Nat → F) (one : rho 0=1)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ bits : Fin 32 → Bool,(∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i)) ∧
 rho 4=MerkleOrdered34.root rho bits 16 := by
 obtain ⟨bits,encoding⟩ := bit_encoding rho satisfied
 refine ⟨bits,encoding,?_⟩
 rw [CapturedMerklePathGlobal187.anchor rho one satisfied,MerkleOrdered34.meaning_eq rho bits encoding 15 (by decide)]
end ShielddSecurity.CapturedMerkleOrderedGlobal189

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleOrderedGlobal189.bit_encoding
#print axioms ShielddSecurity.CapturedMerkleOrderedGlobal189.bit_encoding
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleOrderedGlobal189.ordered_anchor
#print axioms ShielddSecurity.CapturedMerkleOrderedGlobal189.ordered_anchor
