import ShielddSecurity.PublishedPointNonzero587
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RecoveryInverseSeed778
open ConcreteJubjubField01 TransferSem

def family (slot : Fin 2) : Fin 8 := ⟨slot.val,lt_trans slot.isLt (by decide)⟩
def hint (slot : Fin 2) : Nat := if slot.val=0 then 6192 else 7596
def operand (slot : Fin 2) : Nat := if slot.val=0 then 4922 else 6326
def value (w : TransferSem.Witness) (slot : Fin 2) : F := (FixedFamilyPublished579.published w (family slot)).x

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=6192 then (value w 0)⁻¹ else if column=7596 then (value w 1)⁻¹ else original column

theorem selected (original : Nat → F) (w : TransferSem.Witness) (slot : Fin 2) :
    seed original w (hint slot)=(value w slot)⁻¹ := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 := by omega
  rcases cases with rfl|rfl <;> rfl

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (first : column≠6192) (second : column≠7596) : seed original w column=original column := by
  simp only [seed,if_neg first,if_neg second]

theorem nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (slot : Fin 2) : value w slot≠0 :=
  PublishedPointNonzero587.x_nonzero c w legal (family slot)

theorem inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (slot : Fin 2) :
    seed original w (hint slot)*value w slot=1 := by
  rw [selected]
  exact inv_mul_cancel₀ (nonzero c w legal slot)
end ShielddSecurity.RecoveryInverseSeed778

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseSeed778.selected
#print axioms ShielddSecurity.RecoveryInverseSeed778.selected

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseSeed778.outside
#print axioms ShielddSecurity.RecoveryInverseSeed778.outside

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseSeed778.nonzero
#print axioms ShielddSecurity.RecoveryInverseSeed778.nonzero

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseSeed778.inverse
#print axioms ShielddSecurity.RecoveryInverseSeed778.inverse
