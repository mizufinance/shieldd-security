import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.BalanceBlindingDomain670
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserTreeMeaning965
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model PoseidonNatural192.hash Poseidon.hash6 userLeaf

def siblings (user : User) (level : Nat) (slot : Fin 3) : Nat :=
  if h : level<16 then user.siblings ⟨level,h⟩ slot else 0

def value (c : Crypto) (asset : Nat) (user : User) (n : Nat) : Nat :=
  treeRoot c .compliance n user.position (userLeaf c asset user) (siblings user)

theorem zero (c : Crypto) (asset : Nat) (user : User) : value c asset user 0=userLeaf c asset user := rfl

theorem successor (c : Crypto) (asset : Nat) (user : User) (n : Nat) :
    value c asset user (n+1)=c.hash .compliance ([n+1]++QuaternarySelector944.children
      (user.position/4^n%4) (value c asset user n) (siblings user n 0) (siblings user n 1) (siblings user n 2)) := by
  simp only [value,treeRoot,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

theorem final (c : Crypto) (asset : Nat) (user : User) : value c asset user 16=
    root c .compliance user.position (userLeaf c asset user) user.siblings := rfl

theorem children_length {A : Type} (slot : Nat) (node s0 s1 s2 : A) :
    (QuaternarySelector944.children slot node s0 s1 s2).length=4 := by
  unfold QuaternarySelector944.children
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem natural_hash (c : Crypto) (level slot node s0 s1 s2 : Nat) :
    ((BalanceBlindingDomain670.crypto c).hash .compliance
      ([level+1]++QuaternarySelector944.children slot node s0 s1 s2):F)=
    Poseidon.hash6 (RegistryNatural193.wide : Poseidon.Parameters F 6) 3
      ([(level+1:F)]++QuaternarySelector944.children slot (node:F) (s0:F) (s1:F) (s2:F)) := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .compliance ([level+1]++QuaternarySelector944.children slot node s0 s1 s2):F)=_
  rw [PoseidonNatural192.hash_cast]
  have length : (([level+1]++QuaternarySelector944.children slot node s0 s1 s2).map (fun n : Nat => (n:F))).length=5 := by
    simp only [List.length_map,List.length_append,List.length_singleton,children_length]
  unfold Poseidon.hash
  rw [if_neg (by rw [length];decide)]
  simp only [domainCode,List.map_append,List.map_cons,List.map_nil,QuaternarySelector944.map_children,Nat.cast_add,Nat.cast_one]
end ShielddSecurity.UserTreeMeaning965

set_option pp.all true in
#check @ShielddSecurity.UserTreeMeaning965.zero
#print axioms ShielddSecurity.UserTreeMeaning965.zero

set_option pp.all true in
#check @ShielddSecurity.UserTreeMeaning965.successor
#print axioms ShielddSecurity.UserTreeMeaning965.successor

set_option pp.all true in
#check @ShielddSecurity.UserTreeMeaning965.final
#print axioms ShielddSecurity.UserTreeMeaning965.final

set_option pp.all true in
#check @ShielddSecurity.UserTreeMeaning965.children_length
#print axioms ShielddSecurity.UserTreeMeaning965.children_length

set_option pp.all true in
#check @ShielddSecurity.UserTreeMeaning965.natural_hash
#print axioms ShielddSecurity.UserTreeMeaning965.natural_hash
