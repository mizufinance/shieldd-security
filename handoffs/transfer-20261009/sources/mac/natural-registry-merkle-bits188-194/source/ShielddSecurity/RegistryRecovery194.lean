import ShielddSecurity.RegistryNatural193
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryRecovery194
variable {F : Type} [Field F]
open PoseidonNatural192
open CapturedInitial73419Generic01 (p)
def recover (representation : CanonicalRepresentation F) (rho : Nat → F) : TransferSem.AssetLeaf where
 value:=representation.value (rho 11)
 nextIndex:=representation.value (rho 12)
 nextValue:=representation.value (rho 13)
 detection:=⟨representation.value (rho 14),representation.value (rho 15)⟩
 dailyLimit:=representation.value (rho 21)
 routePolicy:=representation.value (rho 22)
 ring:=⟨representation.value (rho 23),representation.value (rho 24)⟩
 ringID:=representation.value (rho 30)
 policyID:=representation.value (rho 31)
 permission:=representation.value (rho 32)
 resource:=representation.value (rho 33)
 audit:=⟨representation.value (rho 34),
   ⟨representation.value (rho 35),representation.value (rho 36)⟩,
   ⟨representation.value (rho 42),representation.value (rho 43)⟩⟩
 position:=representation.value (rho 135)
 siblings:=fun level slot => representation.value (rho (136+3*level.val+slot.val))
theorem roles (representation : CanonicalRepresentation F) (rho : Nat → F) :
 RegistryNatural193.Roles rho (recover representation rho) := by
 constructor <;> exact (representation.cast_value _).symm
theorem position_cast (representation : CanonicalRepresentation F) (rho : Nat → F) :
 ((recover representation rho).position:F)=rho 135 := representation.cast_value _
theorem position_canonical (representation : CanonicalRepresentation F) (rho : Nat → F) :
 (recover representation rho).position<p := by
 exact representation.bounded _
theorem siblings_cast (representation : CanonicalRepresentation F) (rho : Nat → F)
 (level : Fin 16) (slot : Fin 3) :
 ((recover representation rho).siblings level slot:F)=rho (136+3*level.val+slot.val) :=
 representation.cast_value _
theorem leaf_meaning (representation : CanonicalRepresentation F) (rho : Nat → F) (c : TransferSem.Crypto) :
 MerkleInputMeaning28.registryMeaning rho=
 (TransferSem.assetLeaf (withHash c RegistryNatural193.small RegistryNatural193.wide representation)
   (recover representation rho):F) := RegistryNatural193.leaf_meaning rho _ (roles representation rho) c representation
end ShielddSecurity.RegistryRecovery194

set_option pp.all true in
#check @ShielddSecurity.RegistryRecovery194.recover
#print axioms ShielddSecurity.RegistryRecovery194.recover
set_option pp.all true in
#check @ShielddSecurity.RegistryRecovery194.roles
#print axioms ShielddSecurity.RegistryRecovery194.roles
set_option pp.all true in
#check @ShielddSecurity.RegistryRecovery194.position_cast
#print axioms ShielddSecurity.RegistryRecovery194.position_cast
set_option pp.all true in
#check @ShielddSecurity.RegistryRecovery194.position_canonical
#print axioms ShielddSecurity.RegistryRecovery194.position_canonical
set_option pp.all true in
#check @ShielddSecurity.RegistryRecovery194.siblings_cast
#print axioms ShielddSecurity.RegistryRecovery194.siblings_cast
set_option pp.all true in
#check @ShielddSecurity.RegistryRecovery194.leaf_meaning
#print axioms ShielddSecurity.RegistryRecovery194.leaf_meaning
