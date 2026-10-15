import ShielddSecurity.BalanceBlindingDomain670
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserLeafNatural1229
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model PoseidonNatural192.hash Poseidon.hash6

def fields (asset : Nat) (user : User) : List Nat :=
  [user.address.diversified.x,user.address.diversified.y,
   user.address.transmission.x,user.address.transmission.y,asset,
   user.rnkDH.x,user.rnkDH.y,user.rnkCommitment,user.lifecycle]

set_option pp.all true in
#check @ShielddSecurity.UserLeafNatural1229.fields
#print axioms ShielddSecurity.UserLeafNatural1229.fields

theorem leaf_fields (c : Crypto) (asset : Nat) (user : User) :
    userLeaf c asset user=c.hash .complianceLeaf (fields asset user) := rfl

set_option pp.all true in
#check @ShielddSecurity.UserLeafNatural1229.leaf_fields
#print axioms ShielddSecurity.UserLeafNatural1229.leaf_fields

theorem hash_origin (c : Crypto) (inputs : List Nat) :
    (BalanceBlindingDomain670.crypto c).hash .complianceLeaf inputs=
      PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide
        ConcreteRegistrySharedEncoding294.representation .complianceLeaf inputs := rfl

set_option pp.all true in
#check @ShielddSecurity.UserLeafNatural1229.hash_origin
#print axioms ShielddSecurity.UserLeafNatural1229.hash_origin

theorem hash_nine (inputs : List Nat) (length : inputs.length=9) :
    (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide
      ConcreteRegistrySharedEncoding294.representation .complianceLeaf inputs:F)=
    Poseidon.hash6 (RegistryNatural193.wide : Poseidon.Parameters F 6) 19
      (inputs.map (fun x : Nat => (x:F))) := by
  rw [PoseidonNatural192.hash_cast]
  have mappedLength : (inputs.map (fun x : Nat => (x:F))).length=9 := by
    simpa only [List.length_map] using length
  unfold Poseidon.hash
  rw [if_neg (by rw [mappedLength];decide +kernel)]
  rfl

set_option pp.all true in
#check @ShielddSecurity.UserLeafNatural1229.hash_nine
#print axioms ShielddSecurity.UserLeafNatural1229.hash_nine

theorem natural (c : Crypto) (asset : Nat) (user : User) :
    (userLeaf (BalanceBlindingDomain670.crypto c) asset user:F)=
      Poseidon.hash6 (RegistryNatural193.wide : Poseidon.Parameters F 6) 19
        ((fields asset user).map (fun x : Nat => (x:F))) := by
  rw [leaf_fields,hash_origin]
  exact hash_nine (fields asset user) rfl

set_option pp.all true in
#check @ShielddSecurity.UserLeafNatural1229.natural
#print axioms ShielddSecurity.UserLeafNatural1229.natural

end ShielddSecurity.UserLeafNatural1229
