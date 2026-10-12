import ShielddSecurity.RegistryNaturalSeed298
import Mathlib.Tactic.Tauto
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HeaderRegistrySeed299
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

/-- Header observables are taken from the independent semantic witness, never
from the circuit candidate's computed statement column. -/
def header (c : Crypto) (w : TransferSem.Witness) : Nat → F
  | 0 => 1
  | 1 => ((crypto c).hash .transferStatement (publicFields (crypto c) w) : F)
  | 2 => (w.blinding : F)
  | 3 => (w.anchor : F)
  | 4 => (w.assetAnchor : F)
  | 5 => (w.userAnchor : F)
  | 6 => (w.asset : F)
  | 7 => (w.timestamp : F)
  | 8 => (w.nonce : F)
  | 9 => (w.blinding : F)
  | 10 => if w.regulated then 1 else 0
  | _ => 0

def seed (base : Nat → F) (c : Crypto) (w : TransferSem.Witness) (column : Nat) : F :=
  if column = 22737 then header c w 1
  else if column ≤ 10 then header c w column else base column

def combined (base : Nat → F) (c : Crypto) (w : TransferSem.Witness) : Nat → F :=
  RegistryNaturalSeed298.seed (seed base c w) w.registry

theorem seed_outside (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (column : Nat) (outside : 10 < column) (different : column ≠ 22737) :
    seed base c w column = base column := by
  simp only [seed, if_neg different, if_neg (Nat.not_le.mpr outside)]

theorem original_headers (base : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    combined base c w 0 = 1 ∧
    combined base c w 1 = ((crypto c).hash .transferStatement (publicFields (crypto c) w) : F) ∧
    combined base c w 2 = (w.blinding : F) ∧
    combined base c w 3 = (w.anchor : F) ∧
    combined base c w 4 = (w.assetAnchor : F) ∧
    combined base c w 5 = (w.userAnchor : F) ∧
    combined base c w 6 = (w.asset : F) ∧
    combined base c w 7 = (w.timestamp : F) ∧
    combined base c w 8 = (w.nonce : F) ∧
    combined base c w 9 = (w.blinding : F) ∧
    combined base c w 10 = (if w.regulated then 1 else 0) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem public_input_same (base : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    combined base c w 22737 = combined base c w 1 := by
  unfold combined
  rw [RegistryNaturalSeed298.untouched (seed base c w) w.registry 22737 (by decide) (by omega),
    RegistryNaturalSeed298.untouched (seed base c w) w.registry 1 (by decide) (by omega)]
  simp only [seed, if_pos (rfl : (22737 : Nat) = 22737),
    if_neg (by decide : (1 : Nat) ≠ 22737), if_pos (by decide : (1 : Nat) ≤ 10), if_true]

theorem committed_same (base : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    combined base c w 2 = combined base c w 9 := by
  rw [(original_headers base c w).2.2.1, (original_headers base c w).2.2.2.2.2.2.2.2.2.1]

theorem canonical_registry (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    fieldsCanonical (registryFields w.registry) := by
  intro value member
  apply canonical value
  simp only [List.mem_append]
  tauto

theorem recover_registry (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) :
    RegistryRecovery194.recover representation (combined base c w) = w.registry :=
  RegistryNaturalSeed298.recover_seed (seed base c w) w.registry (canonical_registry w canonical)

theorem with_hash_bound {K : Type} [Field K] (small : Poseidon.Parameters K 3)
    (wide : Poseidon.Parameters K 6) (rep : PoseidonNatural192.CanonicalRepresentation K)
    (c : Crypto) (domain : Domain) (values : List Nat) :
    (PoseidonNatural192.withHash c small wide rep).hash domain values < TransferCore.fieldModulus :=
  rep.bounded _

theorem claim_bound (c : Crypto) (w : TransferSem.Witness) :
    (crypto c).hash .transferStatement (publicFields (crypto c) w) < TransferCore.fieldModulus :=
  with_hash_bound _ _ representation _ .transferStatement (publicFields (crypto c) w)

theorem claim_preserved (base : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    representation.value (combined base c w 1) =
      (crypto c).hash .transferStatement (publicFields (crypto c) w) := by
  rw [(original_headers base c w).2.1]
  exact RegistryNaturalSeed298.represented_nat _ (claim_bound c w)

theorem scalar_below_252 : TransferCore.scalarOrder < 2 ^ 252 := by decide +kernel
theorem scalar_below_field : TransferCore.scalarOrder < TransferCore.fieldModulus := by decide +kernel
theorem time_below_field : 2 ^ 64 < TransferCore.fieldModulus := by decide +kernel

theorem legal_timestamp (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    w.timestamp < 2 ^ 64 :=
  legal.2.1.2.2.2.2.2.2.1.1

theorem legal_blinding (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    w.blinding < TransferCore.scalarOrder :=
  legal.2.1.2.2.2.2.2.2.2.2.2.1.2.2.2.2

theorem time_word_bound (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    WordNaturalSeed297.numbers (combined base c w) 7 < 2 ^ 64 := by
  change representation.value (combined base c w 7) < 2 ^ 64
  rw [(original_headers base c w).2.2.2.2.2.2.2.1,
    RegistryNaturalSeed298.represented_nat _ (lt_trans (legal_timestamp c w legal) time_below_field)]
  exact legal_timestamp c w legal

theorem blinding_word_bound (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    WordNaturalSeed297.numbers (combined base c w) 9 < 2 ^ 252 := by
  change representation.value (combined base c w 9) < 2 ^ 252
  rw [(original_headers base c w).2.2.2.2.2.2.2.2.2.1,
    RegistryNaturalSeed298.represented_nat _ (lt_trans (legal_blinding c w legal) scalar_below_field)]
  exact lt_trans (legal_blinding c w legal) scalar_below_252
end ShielddSecurity.HeaderRegistrySeed299


set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.header
#print axioms ShielddSecurity.HeaderRegistrySeed299.header

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.seed
#print axioms ShielddSecurity.HeaderRegistrySeed299.seed

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.combined
#print axioms ShielddSecurity.HeaderRegistrySeed299.combined

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.seed_outside
#print axioms ShielddSecurity.HeaderRegistrySeed299.seed_outside

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.original_headers
#print axioms ShielddSecurity.HeaderRegistrySeed299.original_headers

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.public_input_same
#print axioms ShielddSecurity.HeaderRegistrySeed299.public_input_same

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.committed_same
#print axioms ShielddSecurity.HeaderRegistrySeed299.committed_same

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.canonical_registry
#print axioms ShielddSecurity.HeaderRegistrySeed299.canonical_registry

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.recover_registry
#print axioms ShielddSecurity.HeaderRegistrySeed299.recover_registry

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.with_hash_bound
#print axioms ShielddSecurity.HeaderRegistrySeed299.with_hash_bound

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.claim_bound
#print axioms ShielddSecurity.HeaderRegistrySeed299.claim_bound

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.claim_preserved
#print axioms ShielddSecurity.HeaderRegistrySeed299.claim_preserved

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.scalar_below_252
#print axioms ShielddSecurity.HeaderRegistrySeed299.scalar_below_252

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.scalar_below_field
#print axioms ShielddSecurity.HeaderRegistrySeed299.scalar_below_field

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.time_below_field
#print axioms ShielddSecurity.HeaderRegistrySeed299.time_below_field

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.legal_timestamp
#print axioms ShielddSecurity.HeaderRegistrySeed299.legal_timestamp

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.legal_blinding
#print axioms ShielddSecurity.HeaderRegistrySeed299.legal_blinding

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.time_word_bound
#print axioms ShielddSecurity.HeaderRegistrySeed299.time_word_bound

set_option pp.all true in
#check @ShielddSecurity.HeaderRegistrySeed299.blinding_word_bound
#print axioms ShielddSecurity.HeaderRegistrySeed299.blinding_word_bound
