import ShielddSecurity.CapturedMerkleGlobalLevels185
import ShielddSecurity.CapturedMerkleFirstGlobal186
import ShielddSecurity.MerklePath33Meaning
import ShielddSecurity.CapturedAnchorRowSound165
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerklePathGlobal187
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem rest_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerklePath33.rows (F:=F)) := by
 change Satisfies rho (CompilerSegmentChain33.rows copy (MerklePath33.piece (F:=F)) 15)
 apply CompilerIndexedSlices183.chain_sound
 intro i less
 change Satisfies rho (MerkleFamily32Whole.rows (F:=F) ⟨i%15,Nat.mod_lt i (by decide)⟩)
 exact CapturedMerkleGlobalLevels185.sound rho satisfied _
theorem output (rho : Nat → F) (one : rho 0=1)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 eval rho MerklePath33AnchorData.output=MerklePath33Meaning.meaning rho 15 :=
 MerklePath33Meaning.arbitrary rho one (CapturedMerkleFirstGlobal186.prior_sound rho satisfied)
 (CapturedMerkleFirstGlobal186.sound rho satisfied) (rest_sound rho satisfied)
theorem anchor (rho : Nat → F) (one : rho 0=1)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 rho 4=MerklePath33Meaning.meaning rho 15 :=
 (CapturedAnchorRowSound165.anchor_value rho satisfied).symm.trans (output rho one satisfied)
end ShielddSecurity.CapturedMerklePathGlobal187

set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePathGlobal187.rest_sound
#print axioms ShielddSecurity.CapturedMerklePathGlobal187.rest_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePathGlobal187.output
#print axioms ShielddSecurity.CapturedMerklePathGlobal187.output
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePathGlobal187.anchor
#print axioms ShielddSecurity.CapturedMerklePathGlobal187.anchor
