import ShielddSecurity.MerkleFieldFold196
import ShielddSecurity.CanonicalRecovery195
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleNaturalRoot197
open PoseidonNatural192 RegistryRecovery194
open CapturedInitial73419Generic01 (p)
variable {F : Type} [Field F]
theorem root_cast (representation : CanonicalRepresentation F) (rho : Nat → F) (c : TransferSem.Crypto) :
 (TransferSem.root (withHash c RegistryNatural193.small RegistryNatural193.wide representation) .asset
   (recover representation rho).position
   (TransferSem.assetLeaf (withHash c RegistryNatural193.small RegistryNatural193.wide representation)
     (recover representation rho)) (recover representation rho).siblings:F)=
 CapturedMerkleIntegerRoot191.root rho (recover representation rho).position 16 := by
 unfold TransferSem.root
 rw [treeRoot_cast,←leaf_meaning representation rho c]
 rw [←MerkleFieldFold196.field_root]
 unfold PoseidonNatural192.treeRoot
 apply MerkleFieldFold196.fold_congr
 intro level member node
 have bound : level<16 := List.mem_range.mp member
 simp only [dif_pos bound,RegistryRecovery194.recover,representation.cast_value]
theorem leaf_bound (representation : CanonicalRepresentation F) (rho : Nat → F) (c : TransferSem.Crypto) :
 TransferSem.assetLeaf (withHash c RegistryNatural193.small RegistryNatural193.wide representation)
   (recover representation rho)<TransferCore.fieldModulus := by
 unfold TransferSem.assetLeaf
 exact representation.bounded _
variable [CharP F p]
theorem anchor (representation : CanonicalRepresentation F) (rho : Nat → F)
 (c : TransferSem.Crypto) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 (recover representation rho).position<2^32 ∧
 TransferSem.root (withHash c RegistryNatural193.small RegistryNatural193.wide representation) .asset
   (recover representation rho).position
   (TransferSem.assetLeaf (withHash c RegistryNatural193.small RegistryNatural193.wide representation)
     (recover representation rho)) (recover representation rho).siblings=representation.value (rho 4) := by
 have observed:=CapturedMerkleIntegerRoot191.anchor rho one satisfied
   (recover representation rho).position (position_canonical representation rho) (position_cast representation rho)
 refine ⟨observed.1,?_⟩
 apply Eq.symm
 apply CanonicalRecovery195.value_unique representation (rho 4)
 · exact CanonicalRecovery195.treeRoot_bound c RegistryNatural193.small RegistryNatural193.wide
     representation .asset 16 (recover representation rho).position _ _ (leaf_bound representation rho c)
 · exact (root_cast representation rho c).trans observed.2.symm
end ShielddSecurity.MerkleNaturalRoot197

set_option pp.all true in
#check @ShielddSecurity.MerkleNaturalRoot197.root_cast
#print axioms ShielddSecurity.MerkleNaturalRoot197.root_cast
set_option pp.all true in
#check @ShielddSecurity.MerkleNaturalRoot197.leaf_bound
#print axioms ShielddSecurity.MerkleNaturalRoot197.leaf_bound
set_option pp.all true in
#check @ShielddSecurity.MerkleNaturalRoot197.anchor
#print axioms ShielddSecurity.MerkleNaturalRoot197.anchor
