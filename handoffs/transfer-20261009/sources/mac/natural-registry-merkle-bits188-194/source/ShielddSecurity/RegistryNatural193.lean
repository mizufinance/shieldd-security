import ShielddSecurity.PoseidonNatural192
import ShielddSecurity.MerkleInputMeaning28
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryNatural193
variable {F : Type} [Field F]
open PoseidonNatural192
def fieldLeaf (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
 (l : TransferSem.AssetLeaf) : F :=
 Poseidon.hash6 wide 25 [(l.value:F),(l.nextIndex:F),(l.nextValue:F),
   Poseidon.hash6 wide 23 [(l.detection.x:F),(l.detection.y:F),(l.dailyLimit:F),(l.routePolicy:F)],
   Poseidon.hash3 small 24 [
     Poseidon.hash6 wide 24 [(l.ring.x:F),(l.ring.y:F),(l.ringID:F),(l.policyID:F),(l.permission:F),(l.resource:F)],
     Poseidon.hash6 wide 36 [(l.audit.epoch:F),(l.audit.payload.x:F),(l.audit.payload.y:F),(l.audit.checking.x:F),(l.audit.checking.y:F)]]]
theorem assetLeaf_cast (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F) (l : TransferSem.AssetLeaf) :
 (TransferSem.assetLeaf (withHash c small wide representation) l:F)=fieldLeaf small wide l := by
 simp [TransferSem.assetLeaf,TransferSem.pointFields,withHash_cast,Poseidon.hash,TransferSem.domainCode,fieldLeaf]
structure Roles (rho : Nat → F) (l : TransferSem.AssetLeaf) : Prop where
 value : rho 11=(l.value:F)
 nextIndex : rho 12=(l.nextIndex:F)
 nextValue : rho 13=(l.nextValue:F)
 detectionX : rho 14=(l.detection.x:F)
 detectionY : rho 15=(l.detection.y:F)
 dailyLimit : rho 21=(l.dailyLimit:F)
 routePolicy : rho 22=(l.routePolicy:F)
 ringX : rho 23=(l.ring.x:F)
 ringY : rho 24=(l.ring.y:F)
 ringID : rho 30=(l.ringID:F)
 policyID : rho 31=(l.policyID:F)
 permission : rho 32=(l.permission:F)
 resource : rho 33=(l.resource:F)
 epoch : rho 34=(l.audit.epoch:F)
 payloadX : rho 35=(l.audit.payload.x:F)
 payloadY : rho 36=(l.audit.payload.y:F)
 checkingX : rho 42=(l.audit.checking.x:F)
 checkingY : rho 43=(l.audit.checking.y:F)

def small : Poseidon.Parameters F 3 := Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters
def wide : Poseidon.Parameters F 6 := Poseidon.castParameters TransferPoseidonCall04Shared01.parameters
theorem field_roles (rho : Nat → F) (l : TransferSem.AssetLeaf) (roles : Roles rho l) :
 MerkleInputMeaning28.registryMeaning rho=fieldLeaf small wide l := by
 simp only [MerkleInputMeaning28.registryMeaning,RegistryInputJoin24.semanticInputs,fieldLeaf,small,wide,
 roles.value,roles.nextIndex,roles.nextValue,roles.detectionX,roles.detectionY,roles.dailyLimit,roles.routePolicy,roles.ringX,roles.ringY,roles.ringID,roles.policyID,roles.permission,roles.resource,roles.epoch,roles.payloadX,roles.payloadY,roles.checkingX,roles.checkingY]
theorem leaf_meaning (rho : Nat → F) (l : TransferSem.AssetLeaf) (roles : Roles rho l)
 (c : TransferSem.Crypto) (representation : CanonicalRepresentation F) :
 MerkleInputMeaning28.registryMeaning rho=
 (TransferSem.assetLeaf (withHash c small wide representation) l:F) := by
 rw [assetLeaf_cast]
 exact field_roles rho l roles
end ShielddSecurity.RegistryNatural193

set_option pp.all true in
#check @ShielddSecurity.RegistryNatural193.fieldLeaf
#print axioms ShielddSecurity.RegistryNatural193.fieldLeaf
set_option pp.all true in
#check @ShielddSecurity.RegistryNatural193.assetLeaf_cast
#print axioms ShielddSecurity.RegistryNatural193.assetLeaf_cast
set_option pp.all true in
#check @ShielddSecurity.RegistryNatural193.Roles
#print axioms ShielddSecurity.RegistryNatural193.Roles
set_option pp.all true in
#check @ShielddSecurity.RegistryNatural193.small
#print axioms ShielddSecurity.RegistryNatural193.small
set_option pp.all true in
#check @ShielddSecurity.RegistryNatural193.wide
#print axioms ShielddSecurity.RegistryNatural193.wide
set_option pp.all true in
#check @ShielddSecurity.RegistryNatural193.field_roles
#print axioms ShielddSecurity.RegistryNatural193.field_roles
set_option pp.all true in
#check @ShielddSecurity.RegistryNatural193.leaf_meaning
#print axioms ShielddSecurity.RegistryNatural193.leaf_meaning
