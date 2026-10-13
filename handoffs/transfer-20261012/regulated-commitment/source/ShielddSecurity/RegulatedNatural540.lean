import ShielddSecurity.AuthorizationIncomingHash532
import ShielddSecurity.AuthorizationHash530C56
import ShielddSecurity.AuthorizationHash530C57
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegulatedNatural540
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model PoseidonNatural192.hash Poseidon.hash6 Poseidon.hash3

theorem key_hash (c : Crypto) (values : List Nat) (length : values.length=9) :
    ((AuthorizationFixedDomain485.crypto c).hash .regulatedNullifierKey values:F)=
      Poseidon.hash6 (Poseidon.castParameters AuthorizationHash530C56.parameters) 17
        (values.map fun (x : Nat) => (x:F)) := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide representation
    .regulatedNullifierKey values:F)=_
  rw [show Poseidon.castParameters AuthorizationHash530C56.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by rw [List.length_map,length];decide)]
  simp [domainCode]
set_option pp.all true in
#check @key_hash
#print axioms key_hash

theorem commitment_hash (c : Crypto) (value : Nat) :
    ((AuthorizationFixedDomain485.crypto c).hash .regulatedNullifierCommitment [value]:F)=
      Poseidon.hash3 (Poseidon.castParameters AuthorizationHash530C57.parameters) 18 [(value:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide representation
    .regulatedNullifierCommitment [value]:F)=_
  rw [show Poseidon.castParameters AuthorizationHash530C57.parameters=(RegistryNatural193.small : Poseidon.Parameters F 3) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_pos (by change 1 ≤ 2;decide)]
  rfl
set_option pp.all true in
#check @commitment_hash
#print axioms commitment_hash
end ShielddSecurity.RegulatedNatural540
