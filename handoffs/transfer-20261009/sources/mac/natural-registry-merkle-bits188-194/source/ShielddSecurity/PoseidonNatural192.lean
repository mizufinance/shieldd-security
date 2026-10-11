import ShielddSecurity.Poseidon
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PoseidonNatural192
variable {F : Type} [Field F]
structure CanonicalRepresentation (F : Type) [Field F] where
 value : F → Nat
 bounded : ∀ x, value x<TransferCore.fieldModulus
 cast_value : ∀ x, (value x : F)=x
def hash (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
 (representation : CanonicalRepresentation F) (domain : TransferSem.Domain) (inputs : List Nat) : Nat :=
 representation.value (Poseidon.hash small wide (TransferSem.domainCode domain) (inputs.map fun (x : Nat) => (x:F)))
theorem hash_cast (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
 (representation : CanonicalRepresentation F) (domain : TransferSem.Domain) (inputs : List Nat) :
 (hash small wide representation domain inputs:F)=
 Poseidon.hash small wide (TransferSem.domainCode domain) (inputs.map fun (x : Nat) => (x:F)) :=
 representation.cast_value _
theorem hash_bound (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
 (representation : CanonicalRepresentation F) (domain : TransferSem.Domain) (inputs : List Nat) :
 hash small wide representation domain inputs<TransferCore.fieldModulus := representation.bounded _
def withHash (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F) : TransferSem.Crypto :=
 {c with hash:=hash small wide representation}
theorem withHash_cast (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F)
 (domain : TransferSem.Domain) (inputs : List Nat) :
 ((withHash c small wide representation).hash domain inputs:F)=
 Poseidon.hash small wide (TransferSem.domainCode domain) (inputs.map fun (x : Nat) => (x:F)) :=
 hash_cast small wide representation domain inputs
theorem fold_cast (items : List Nat) (naturalStep : Nat → Nat → Nat) (fieldStep : F → Nat → F)
 (step : ∀ node level, (naturalStep node level:F)=fieldStep (node:F) level) (initial : Nat) :
 ((items.foldl naturalStep initial : Nat):F)=items.foldl fieldStep (initial:F) := by
 induction items generalizing initial with
 | nil => rfl
 | cons head tail ih =>
   rw [List.foldl_cons,List.foldl_cons,ih,step]
def treeRoot (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
 (domain : TransferSem.Domain) (depth position : Nat) (leaf : F) (siblings : Nat → Fin 3 → F) : F :=
 (List.range depth).foldl (fun node level =>
   let slot:=position/4^level%4
   let children:=if slot=0 then [node,siblings level 0,siblings level 1,siblings level 2]
     else if slot=1 then [siblings level 0,node,siblings level 1,siblings level 2]
     else if slot=2 then [siblings level 0,siblings level 1,node,siblings level 2]
     else [siblings level 0,siblings level 1,siblings level 2,node]
   Poseidon.hash small wide (TransferSem.domainCode domain) ([((level+1:Nat):F)]++children)) leaf
theorem treeRoot_cast (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F)
 (domain : TransferSem.Domain) (depth position leaf : Nat) (siblings : Nat → Fin 3 → Nat) :
 (TransferSem.treeRoot (withHash c small wide representation) domain depth position leaf siblings:F)=
 treeRoot small wide domain depth position (leaf:F) (fun level slot => (siblings level slot:F)) := by
 unfold TransferSem.treeRoot treeRoot
 apply fold_cast
 intro node level
 rw [withHash_cast]
 congr 1
 split_ifs <;> simp only [List.map_append,List.map_cons,List.map_nil]
end ShielddSecurity.PoseidonNatural192

set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.CanonicalRepresentation
#print axioms ShielddSecurity.PoseidonNatural192.CanonicalRepresentation
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.hash
#print axioms ShielddSecurity.PoseidonNatural192.hash
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.hash_cast
#print axioms ShielddSecurity.PoseidonNatural192.hash_cast
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.hash_bound
#print axioms ShielddSecurity.PoseidonNatural192.hash_bound
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.withHash
#print axioms ShielddSecurity.PoseidonNatural192.withHash
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.withHash_cast
#print axioms ShielddSecurity.PoseidonNatural192.withHash_cast
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.fold_cast
#print axioms ShielddSecurity.PoseidonNatural192.fold_cast
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.treeRoot
#print axioms ShielddSecurity.PoseidonNatural192.treeRoot
set_option pp.all true in
#check @ShielddSecurity.PoseidonNatural192.treeRoot_cast
#print axioms ShielddSecurity.PoseidonNatural192.treeRoot_cast
