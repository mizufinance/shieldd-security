import ShielddSecurity.UserPathConstruction365
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthScalarSeed366
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def values : List Nat := [1994,1995,3766]
def value (w : TransferSem.Witness) (column : Nat) : Nat :=
  if column=1994 then w.auth.quotient
  else if column=1995 then w.auth.ivk
  else if column=3766 then w.auth.randomizer
  else 0

def width (column : Nat) : Nat := if column=1994 then 4 else 252

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column∈values then (value w column:F) else original column

theorem seed_value (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (member : column∈values) :
    seed original w column=(value w column:F) := if_pos member

theorem seed_outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (outside : column∉values) :
    seed original w column=original column := if_neg outside

theorem legal_bounds (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    w.auth.quotient<2^4 ∧ w.auth.ivk<2^252 ∧ w.auth.randomizer<2^252 := by
  rcases legal.2.1.2.2.2.1 with ⟨_,_,_,_,scalar,_,_,_,random,_,_,_⟩
  have quotient : w.auth.quotient≤8 := scalar.2.2.1
  refine ⟨?_,lt_trans scalar.1 HeaderRegistrySeed299.scalar_below_252,lt_trans random HeaderRegistrySeed299.scalar_below_252⟩
  change w.auth.quotient<16
  omega

theorem value_bound (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w)
    (column : Nat) (member : column∈values) : value w column<2^width column := by
  have bounds := legal_bounds c w legal
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact bounds.1
  · exact bounds.2.1
  · exact bounds.2.2

theorem width_below_field (column : Nat) : 2^width column<TransferCore.fieldModulus := by
  unfold width
  split <;> decide +kernel

theorem widths_checked : CapturedWordRoot213.words.all (fun entry => decide
    (entry.1.value∈values → entry.1.width=width entry.1.value)) = true := by decide +kernel

theorem word_width (entry : WordHints210.Slot × Nat) (member : entry∈CapturedWordRoot213.words)
    (auth : entry.1.value∈values) : entry.1.width=width entry.1.value :=
  (of_decide_eq_true (List.all_eq_true.mp widths_checked entry member)) auth

end ShielddSecurity.AuthScalarSeed366

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.values
#print axioms ShielddSecurity.AuthScalarSeed366.values

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.value
#print axioms ShielddSecurity.AuthScalarSeed366.value

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.width
#print axioms ShielddSecurity.AuthScalarSeed366.width

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.seed
#print axioms ShielddSecurity.AuthScalarSeed366.seed

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.seed_value
#print axioms ShielddSecurity.AuthScalarSeed366.seed_value

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.seed_outside
#print axioms ShielddSecurity.AuthScalarSeed366.seed_outside

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.legal_bounds
#print axioms ShielddSecurity.AuthScalarSeed366.legal_bounds

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.value_bound
#print axioms ShielddSecurity.AuthScalarSeed366.value_bound

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.width_below_field
#print axioms ShielddSecurity.AuthScalarSeed366.width_below_field

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.widths_checked
#print axioms ShielddSecurity.AuthScalarSeed366.widths_checked

set_option pp.all true in
#check @ShielddSecurity.AuthScalarSeed366.word_width
#print axioms ShielddSecurity.AuthScalarSeed366.word_width
