from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-merkle-natural-root197-source01'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
body='''import ShielddSecurity.MerkleFieldFold196
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
'''
pins=[W/'mac-merkle-field-fold196-source01/source-root/ShielddSecurity/MerkleFieldFold196.lean',W/'mac-canonical-recovery195-source01/source-root/ShielddSecurity/CanonicalRecovery195.lean',W/'mac-registry-recovery194-source01/source-root/ShielddSecurity/RegistryRecovery194.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'MerkleNaturalRoot197':dict(body=body,names=['root_cast','leaf_bound','anchor'])},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Full captured relation and rho0=1 imply recovered integer position bound and actual TransferSem asset-root equality under explicit canonical representation and same pinned Poseidon parameters. No desired-root or RegistrySem premise. Representation existence, point interpretation, other semantics, SDK/native, legal total constructor remain open. Three planned audits unrun.'),sort_keys=True,separators=(',',':'))+'\n')
