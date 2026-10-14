import ShielddSecurity.CheckingGroupDomain595
import ShielddSecurity.UserPointDomain351
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingInverseSeed783
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model

def hint (slot : Fin 2) : Nat := if slot.val=0 then 9057 else 10589
def value (c : Crypto) (w : TransferSem.Witness) : F := (CheckingGroupDomain595.selected c w).x

theorem selected_nonidentity (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    nonidentity (CheckingGroupDomain595.selected c w) := by
  obtain ⟨_,_,_,_,_,_,_,_,encryption,_⟩ := legal.2.1
  have ownership := encryption.2.2.2.2.2.2.2 (0 : Fin 2)
  exact ownership.2.2.2.1

theorem nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) : value c w≠0 := by
  have nonzero := selected_nonidentity c w legal
  change ((if w.regulated then w.registry.audit.checking else CapturedRegistryPointDomain75.sink).x:F)≠0
  cases flag : w.regulated
  · change (49822839976625491399435002605169580882773999909559575334089637637825427273330:F)≠0
    decide +kernel
  · have valid : ValidPoint (AuthorizationFixedDomain485.crypto c) w.registry.audit.checking := legal.2.1.1.2.2.2.1
    have member := SubgroupSeedCompletion203.member_of_valid
      (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c))
      representation model w.registry.audit.checking valid
    have identity : nonidentity w.registry.audit.checking := by
      change nonidentity (if w.regulated then w.registry.audit.checking else CapturedRegistryPointDomain75.sink) at nonzero
      simpa only [flag,if_true] using nonzero
    exact SubgroupNonidentity350.member_x_nonzero model _ member
      (UserPointDomain351.field_nonidentity _ valid.1 identity)

def seed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=9057 then (value c w)⁻¹ else if column=10589 then (value c w)⁻¹ else original column

theorem selected (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (slot : Fin 2) :
    seed original c w (hint slot)=(value c w)⁻¹ := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 := by omega
  rcases cases with rfl|rfl <;> rfl

theorem outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (column : Nat)
    (first : column≠9057) (second : column≠10589) : seed original c w column=original column := by
  simp only [seed,if_neg first,if_neg second]

theorem inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (slot : Fin 2) :
    seed original c w (hint slot)*value c w=1 := by
  rw [selected]
  exact inv_mul_cancel₀ (nonzero c w legal)
end ShielddSecurity.CheckingInverseSeed783

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseSeed783.selected_nonidentity
#print axioms ShielddSecurity.CheckingInverseSeed783.selected_nonidentity

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseSeed783.nonzero
#print axioms ShielddSecurity.CheckingInverseSeed783.nonzero

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseSeed783.selected
#print axioms ShielddSecurity.CheckingInverseSeed783.selected

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseSeed783.outside
#print axioms ShielddSecurity.CheckingInverseSeed783.outside

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseSeed783.inverse
#print axioms ShielddSecurity.CheckingInverseSeed783.inverse
