import ShielddSecurity.AuthScalarConstruction368
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RemainingWordSeed369
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

/-- Independent integer magnitude, without field subtraction or a row conclusion. -/
def magnitude (w : TransferSem.Witness) : Nat :=
  let input := (w.spends 0).amount + (w.spends 1).amount
  let output := (w.outputs 0).amount + (w.outputs 1).amount
  if output ≤ input then input-output else output-input

def values : List Nat := [4281,4411,4534,4664,4789,4930,6194,6334,7608,7609,7741,7742,8256,8387,8551,10083,11611,13629,14891,16153,19848,19849,21712]
def value (w : TransferSem.Witness) (column : Nat) : Nat :=
  if column=4281 then (w.spends 0).amount
  else if column=4411 then (w.spends 0).position
  else if column=4534 then (w.spends 1).amount
  else if column=4664 then (w.spends 1).position
  else if column=4789 then (w.outputs 0).amount
  else if column=4930 then (w.outputs 0).recovery.randomizer
  else if column=6194 then (w.outputs 1).amount
  else if column=6334 then (w.outputs 1).recovery.randomizer
  else if column=7608 then w.volume.dayIndex
  else if column=7609 then w.volume.second
  else if column=7741 then w.volume.prior
  else if column=7742 then w.volume.successor
  else if column=8256 then BoundedLimbComparison119.difference 128 (w.volume.prior+(w.outputs 0).amount) w.registry.dailyLimit
  else if column=8387 then w.volume.priorPosition
  else if column=8551 then (w.encryption.tiers 0).ephemeral
  else if column=10083 then (w.encryption.tiers 1).ephemeral
  else if column=11611 then (w.encryption.tiers 2).ephemeral
  else if column=13629 then (w.encryption.tiers 3).ephemeral
  else if column=14891 then (w.encryption.ownership 0).randomness
  else if column=16153 then (w.encryption.ownership 1).randomness
  else if column=19848 then w.routing.tags 0
  else if column=19849 then w.routing.tags 1
  else if column=21712 then magnitude w
  else 0

def width (column : Nat) : Nat :=
  if column=4411 ∨ column=4664 ∨ column=7608 ∨ column=8387 then 48
  else if column=4930 ∨ column=6334 ∨ column=8551 ∨ column=10083 ∨ column=11611 ∨ column=13629 ∨ column=14891 ∨ column=16153 then 252
  else if column=7609 then 17
  else if column=19848 ∨ column=19849 then 32
  else if column=21712 then 129
  else 128

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column∈values then (value w column:F) else original column

theorem seed_value (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (member : column∈values) :
    seed original w column=(value w column:F) := if_pos member

theorem seed_outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (outside : column∉values) :
    seed original w column=original column := if_neg outside

theorem magnitude_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : magnitude w < 2^129 := by
  have inputs := legal.2.1.2.2.2.2.1
  have outputs := legal.2.1.2.2.2.2.2.1
  have i0 := (inputs 0).1
  have i1 := (inputs 1).1
  have o0 := (outputs 0).1
  have o1 := (outputs 1).1
  change (w.spends 0).amount < 2^128 at i0
  change (w.spends 1).amount < 2^128 at i1
  change (w.outputs 0).amount < 2^128 at o0
  change (w.outputs 1).amount < 2^128 at o1
  have power : 2^129=2*2^128 := by decide
  rw [power]
  unfold magnitude
  dsimp only
  split <;> omega

theorem value_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (column : Nat) (member : column∈values) :
    value w column < 2^width column := by
  have spends := legal.2.1.2.2.2.2.1
  have outputs := legal.2.1.2.2.2.2.2.1
  have volume := legal.2.1.2.2.2.2.2.2.1
  have routing := legal.2.1.2.2.2.2.2.2.2.1
  have encryption := legal.2.1.2.2.2.2.2.2.2.2.1
  rcases volume with ⟨_,day,second,_,_,_,_,prior,successor,limit,candidate,position,_,_,_⟩
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (spends 0).1
  · exact (spends 0).2.1
  · exact (spends 1).1
  · exact (spends 1).2.1
  · exact (outputs 0).1
  · exact lt_trans (outputs 0).2.2.2.1 HeaderRegistrySeed299.scalar_below_252
  · exact (outputs 1).1
  · exact lt_trans (outputs 1).2.2.2.1 HeaderRegistrySeed299.scalar_below_252
  · exact day
  · change w.volume.second<2^17
    have last : 86399<2^17 := by decide
    exact lt_of_le_of_lt second last
  · exact prior
  · exact successor
  · exact BoundedLimbComparison119.difference_bound 128 _ _ candidate limit
  · exact position
  · exact lt_trans (encryption.2.2.2.2.2.2.1 0).1 HeaderRegistrySeed299.scalar_below_252
  · exact lt_trans (encryption.2.2.2.2.2.2.1 1).1 HeaderRegistrySeed299.scalar_below_252
  · exact lt_trans (encryption.2.2.2.2.2.2.1 2).1 HeaderRegistrySeed299.scalar_below_252
  · exact lt_trans (encryption.2.2.2.2.2.2.1 3).1 HeaderRegistrySeed299.scalar_below_252
  · exact lt_trans (encryption.2.2.2.2.2.2.2 0).1 HeaderRegistrySeed299.scalar_below_252
  · exact lt_trans (encryption.2.2.2.2.2.2.2 1).1 HeaderRegistrySeed299.scalar_below_252
  · exact (routing.2.2.2 0).1
  · exact (routing.2.2.2 1).1
  · exact magnitude_bound c w legal

theorem width_below_field (column : Nat) : 2^width column<TransferCore.fieldModulus := by
  unfold width
  split <;> first | decide +kernel | (split <;> first | decide +kernel | (split <;> first | decide +kernel | (split <;> first | decide +kernel | (split <;> decide +kernel))))

theorem widths_checked : CapturedWordRoot213.words.all (fun entry => decide
    (entry.1.value∈values → entry.1.width=width entry.1.value)) = true := by decide +kernel

theorem word_width (entry : WordHints210.Slot × Nat) (member : entry∈CapturedWordRoot213.words)
    (remaining : entry.1.value∈values) : entry.1.width=width entry.1.value :=
  (of_decide_eq_true (List.all_eq_true.mp widths_checked entry member)) remaining

theorem coverage_checked : CapturedWordRoot213.words.all (fun entry => decide
    (¬LegalWordNormalization272.Alias entry.1.value → entry.1.width<255 →
     entry.1.value∉HeaderSharedConstruction300.knownValues →
     entry.1.value∉RegistryComparisonSeed318.comparisonValues →
     entry.1.value∉UserWordSeed342.values → entry.1.value∉AuthScalarSeed366.values →
     entry.1.value∈values)) = true := by decide +kernel

end ShielddSecurity.RemainingWordSeed369

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.magnitude
#print axioms ShielddSecurity.RemainingWordSeed369.magnitude

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.values
#print axioms ShielddSecurity.RemainingWordSeed369.values

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.value
#print axioms ShielddSecurity.RemainingWordSeed369.value

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.width
#print axioms ShielddSecurity.RemainingWordSeed369.width

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.seed
#print axioms ShielddSecurity.RemainingWordSeed369.seed

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.seed_value
#print axioms ShielddSecurity.RemainingWordSeed369.seed_value

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.seed_outside
#print axioms ShielddSecurity.RemainingWordSeed369.seed_outside

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.magnitude_bound
#print axioms ShielddSecurity.RemainingWordSeed369.magnitude_bound

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.value_bound
#print axioms ShielddSecurity.RemainingWordSeed369.value_bound

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.width_below_field
#print axioms ShielddSecurity.RemainingWordSeed369.width_below_field

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.widths_checked
#print axioms ShielddSecurity.RemainingWordSeed369.widths_checked

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.word_width
#print axioms ShielddSecurity.RemainingWordSeed369.word_width

set_option pp.all true in
#check @ShielddSecurity.RemainingWordSeed369.coverage_checked
#print axioms ShielddSecurity.RemainingWordSeed369.coverage_checked
