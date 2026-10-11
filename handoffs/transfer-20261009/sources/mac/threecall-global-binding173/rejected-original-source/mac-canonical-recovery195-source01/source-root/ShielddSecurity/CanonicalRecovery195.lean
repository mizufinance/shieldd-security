import ShielddSecurity.PoseidonNatural192
import ShielddSecurity.CapturedEpochHints62
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalRecovery195
open PoseidonNatural192
open CapturedInitial73419Generic01 (p)
variable {F : Type} [Field F] [CharP F p]
theorem value_unique (representation : CanonicalRepresentation F) (x : F) (n : Nat)
 (bound : n<p) (equal : (n:F)=x) : representation.value x=n :=
 CapturedEpochHints62.cast_small_unique _ n (representation.bounded x) bound
   ((representation.cast_value x).trans equal.symm)
theorem value_cast (representation : CanonicalRepresentation F) (n : Nat) (bound : n<p) :
 representation.value (n:F)=n := value_unique representation (n:F) n bound rfl
theorem nat_cast_iff (left right : Nat) (leftBound : left<p) (rightBound : right<p) :
 (left:F)=(right:F) ↔ left=right :=
 ⟨CapturedEpochHints62.cast_small_unique left right leftBound rightBound,fun h => congrArg (fun n : Nat => (n:F)) h⟩
theorem value_injective (representation : CanonicalRepresentation F) (x y : F)
 (equal : representation.value x=representation.value y) : x=y :=
 (representation.cast_value x).symm.trans
   ((congrArg (fun n : Nat => (n:F)) equal).trans (representation.cast_value y))
theorem fold_bound (items : List Nat) (step : Nat → Nat → Nat)
 (bounded : ∀ node level,step node level<TransferCore.fieldModulus) (initial : Nat)
 (initialBound : initial<TransferCore.fieldModulus) :
 items.foldl step initial<TransferCore.fieldModulus := by
 induction items generalizing initial with
 | nil => exact initialBound
 | cons head tail ih =>
   exact ih (step initial head) (bounded initial head)
theorem treeRoot_bound (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F)
 (domain : TransferSem.Domain) (depth position leaf : Nat) (siblings : Nat → Fin 3 → Nat)
 (leafBound : leaf<TransferCore.fieldModulus) :
 TransferSem.treeRoot (withHash c small wide representation) domain depth position leaf siblings<TransferCore.fieldModulus := by
 unfold TransferSem.treeRoot
 apply fold_bound
 · intro node level
   exact representation.bounded _
 · exact leafBound
theorem treeRoot_eq_of_cast (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F)
 (domain : TransferSem.Domain) (depth position leaf claimed : Nat) (siblings : Nat → Fin 3 → Nat)
 (leafBound : leaf<TransferCore.fieldModulus) (claimedBound : claimed<TransferCore.fieldModulus)
 (fieldEqual : treeRoot small wide domain depth position (leaf:F)
   (fun level slot => (siblings level slot:F))=(claimed:F)) :
 TransferSem.treeRoot (withHash c small wide representation) domain depth position leaf siblings=claimed := by
 apply CapturedEpochHints62.cast_small_unique _ claimed
   (treeRoot_bound c small wide representation domain depth position leaf siblings leafBound) claimedBound
 exact (treeRoot_cast c small wide representation domain depth position leaf siblings).trans fieldEqual
end ShielddSecurity.CanonicalRecovery195

set_option pp.all true in
#check @ShielddSecurity.CanonicalRecovery195.value_unique
#print axioms ShielddSecurity.CanonicalRecovery195.value_unique
set_option pp.all true in
#check @ShielddSecurity.CanonicalRecovery195.value_cast
#print axioms ShielddSecurity.CanonicalRecovery195.value_cast
set_option pp.all true in
#check @ShielddSecurity.CanonicalRecovery195.nat_cast_iff
#print axioms ShielddSecurity.CanonicalRecovery195.nat_cast_iff
set_option pp.all true in
#check @ShielddSecurity.CanonicalRecovery195.value_injective
#print axioms ShielddSecurity.CanonicalRecovery195.value_injective
set_option pp.all true in
#check @ShielddSecurity.CanonicalRecovery195.fold_bound
#print axioms ShielddSecurity.CanonicalRecovery195.fold_bound
set_option pp.all true in
#check @ShielddSecurity.CanonicalRecovery195.treeRoot_bound
#print axioms ShielddSecurity.CanonicalRecovery195.treeRoot_bound
set_option pp.all true in
#check @ShielddSecurity.CanonicalRecovery195.treeRoot_eq_of_cast
#print axioms ShielddSecurity.CanonicalRecovery195.treeRoot_eq_of_cast
