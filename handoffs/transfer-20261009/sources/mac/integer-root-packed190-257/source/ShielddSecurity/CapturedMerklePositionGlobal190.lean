import ShielddSecurity.CapturedMerkleBitsGlobal188
import ShielddSecurity.CapturedMerklePathGlobal187
import ShielddSecurity.MerkleOrdered34
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerklePositionGlobal190
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def bits (n : Nat) (i : Fin 32) : Bool := (encodeBits 32 n)[i.val]'(by rw [encodeBits_length];exact i.isLt)
variable {F : Type} [Field F] [CharP F p]
theorem encoding (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (n : Nat) (canonical : n<p) (meaning : (n:F)=rho 135) (i : Fin 32) :
 rho (184+i.val)=MerkleQuaternary30.boolValue (bits n i) := by
 have equal := CapturedMerkleBitsGlobal188.bit_fields rho satisfied n canonical meaning
 have each := congrArg (fun xs : List F => xs[i.val]?) equal
 change (MerkleBits29.columns.map rho)[i.val]? = ((encodeBits 32 n).map (fun bit => if bit then (1:F) else 0))[i.val]? at each
 have leftBound : i.val<(MerkleBits29.columns.map rho).length := by
   rw [List.length_map,MerkleBits29.counts.2.2.2]
   exact i.isLt
 have rightBound : i.val<((encodeBits 32 n).map (fun bit => if bit then (1:F) else 0)).length := by
   simpa only [List.length_map,encodeBits_length] using i.isLt
 rw [List.getElem?_eq_getElem leftBound,List.getElem?_eq_getElem rightBound] at each
 have same := Option.some.inj each
 simpa only [List.getElem_map,MerkleBits29.columns,List.getElem_range',Nat.one_mul,bits,MerkleQuaternary30.boolValue] using same
theorem anchor (rho : Nat → F) (one : rho 0=1)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (n : Nat) (canonical : n<p) (meaning : (n:F)=rho 135) :
 n<2^32 ∧ rho 4=MerkleOrdered34.root rho (bits n) 16 := by
 refine ⟨CapturedMerkleBitsGlobal188.canonical_position rho satisfied n canonical meaning,?_⟩
 rw [CapturedMerklePathGlobal187.anchor rho one satisfied,
   MerkleOrdered34.meaning_eq rho (bits n) (encoding rho satisfied n canonical meaning) 15 (by decide)]
end ShielddSecurity.CapturedMerklePositionGlobal190

set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePositionGlobal190.bits
#print axioms ShielddSecurity.CapturedMerklePositionGlobal190.bits
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePositionGlobal190.encoding
#print axioms ShielddSecurity.CapturedMerklePositionGlobal190.encoding
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePositionGlobal190.anchor
#print axioms ShielddSecurity.CapturedMerklePositionGlobal190.anchor
