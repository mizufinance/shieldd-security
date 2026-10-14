import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.VolumePathBits943
import ShielddSecurity.VolumePriorValues909
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathMeaning946
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model PoseidonNatural192.hash Poseidon.hash6 volumeState

def siblings (w : TransferSem.Witness) (level : Nat) (slot : Fin 3) : Nat :=
  if h : level<24 then w.volume.priorSiblings ⟨level,h⟩ slot else 0

def value (c : Crypto) (w : TransferSem.Witness) (n : Nat) : Nat :=
  treeRoot c .state n w.volume.priorPosition
    (volumeState c w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding) (siblings w)

theorem zero (c : Crypto) (w : TransferSem.Witness) : value c w 0=
    volumeState c w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding := rfl

theorem successor (c : Crypto) (w : TransferSem.Witness) (n : Nat) :
    value c w (n+1)=c.hash .state ([n+1]++QuaternarySelector944.children
      (w.volume.priorPosition/4^n%4) (value c w n) (siblings w n 0) (siblings w n 1) (siblings w n 2)) := by
  simp only [value,treeRoot,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

theorem final (c : Crypto) (w : TransferSem.Witness) : value c w 24=
    root c .state w.volume.priorPosition
      (volumeState c w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding) w.volume.priorSiblings := rfl

theorem children_length {A : Type} (slot : Nat) (node s0 s1 s2 : A) :
    (QuaternarySelector944.children slot node s0 s1 s2).length=4 := by
  unfold QuaternarySelector944.children
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem natural_hash (c : Crypto) (level slot node s0 s1 s2 : Nat) :
    ((BalanceBlindingDomain670.crypto c).hash .state
      ([level+1]++QuaternarySelector944.children slot node s0 s1 s2):F)=
    Poseidon.hash6 (RegistryNatural193.wide : Poseidon.Parameters F 6) 1
      ([(level+1:F)]++QuaternarySelector944.children slot (node:F) (s0:F) (s1:F) (s2:F)) := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .state ([level+1]++QuaternarySelector944.children slot node s0 s1 s2):F)=_
  rw [PoseidonNatural192.hash_cast]
  have length : (([level+1]++QuaternarySelector944.children slot node s0 s1 s2).map (fun n : Nat => (n:F))).length=5 := by
    simp only [List.length_map,List.length_append,List.length_singleton,children_length]
  unfold Poseidon.hash
  rw [if_neg (by rw [length];decide)]
  simp only [domainCode,List.map_append,List.map_cons,List.map_nil,QuaternarySelector944.map_children,Nat.cast_add,Nat.cast_one]
end ShielddSecurity.VolumePathMeaning946

set_option pp.all true in
#check @ShielddSecurity.VolumePathMeaning946.zero
#print axioms ShielddSecurity.VolumePathMeaning946.zero

set_option pp.all true in
#check @ShielddSecurity.VolumePathMeaning946.successor
#print axioms ShielddSecurity.VolumePathMeaning946.successor

set_option pp.all true in
#check @ShielddSecurity.VolumePathMeaning946.final
#print axioms ShielddSecurity.VolumePathMeaning946.final

set_option pp.all true in
#check @ShielddSecurity.VolumePathMeaning946.children_length
#print axioms ShielddSecurity.VolumePathMeaning946.children_length

set_option pp.all true in
#check @ShielddSecurity.VolumePathMeaning946.natural_hash
#print axioms ShielddSecurity.VolumePathMeaning946.natural_hash
