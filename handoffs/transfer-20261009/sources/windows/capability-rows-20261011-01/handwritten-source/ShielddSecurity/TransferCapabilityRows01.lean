import ShielddSecurity.TransferAcceptance
import Init.Data.List.Sort

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCapabilityRows01
open TransferAcceptance

/-! Independent executable slot-map validation corresponding to the successful
path of stateless_cache::validate_proof_capability_rows. The accumulator represents
the finite map without choosing its iteration order. Duplicate insertion returns
failure; sorted-key comparison models ordered BTreeMap key equality. BoundRows
is derived, never supplied as a validation premise. Native ProofSlot ordering,
BTreeMap operations, extracted proof locations and primitive Item byte equality
remain global Rust refinement obligations. No verifier soundness is inferred.
The local map on a rejected duplicate is discarded, so no error-state claim is made. -/

def keys (rows : List (Nat × Capability)) : List Nat := rows.map Prod.fst

def collect : List (Nat × Capability) → List (Nat × Capability) →
    Option (List (Nat × Capability))
  | [], accumulated => some accumulated
  | row :: rest, accumulated =>
      if row.1 ∈ keys accumulated then none
      else collect rest (row :: accumulated)

theorem collect_success (rows accumulated result : List (Nat × Capability))
    (unique : (keys accumulated).Nodup)
    (success : collect rows accumulated = some result) :
    (keys result).Nodup ∧ result.Perm (rows ++ accumulated) := by
  induction rows generalizing accumulated with
  | nil =>
      have same : accumulated = result := Option.some.inj success
      subst result
      exact ⟨unique, List.Perm.refl accumulated⟩
  | cons row rest ih =>
      by_cases duplicate : row.1 ∈ keys accumulated
      · simp only [collect, if_pos duplicate] at success
        cases success
      · have tail : collect rest (row :: accumulated) = some result :=
          by simpa only [collect, if_neg duplicate] using success
        have extended : (keys (row :: accumulated)).Nodup :=
          List.nodup_cons.mpr ⟨duplicate, unique⟩
        obtain ⟨distinct, retained⟩ := ih (row :: accumulated) extended tail
        exact ⟨distinct, retained.trans List.perm_middle⟩

def sortedKeys (rows : List (Nat × Capability)) : List Nat :=
  (keys rows).mergeSort (fun left right => left ≤ right)

def checkBindings (registry : Nat) (expected : Nat → Item) (families : Nat → Nat) :
    List (Nat × Capability) → Option Unit
  | [] => some ()
  | row :: rest =>
      if row.2.registry = registry ∧ row.2.item.family = families row.1 ∧ row.2.item = expected row.1 then
        checkBindings registry expected families rest
      else none

theorem check_bindings_success (registry : Nat) (expected : Nat → Item) (families : Nat → Nat)
    (rows : List (Nat × Capability))
    (success : checkBindings registry expected families rows = some ()) :
    ∀ row ∈ rows, row.2.registry = registry ∧ row.2.item.family = families row.1 ∧ row.2.item = expected row.1 := by
  induction rows with
  | nil => simp
  | cons first rest ih =>
      by_cases bound : first.2.registry = registry ∧ first.2.item.family = families first.1 ∧ first.2.item = expected first.1
      · have tail : checkBindings registry expected families rest = some () :=
          by simpa only [checkBindings, if_pos bound] using success
        intro row inside
        rcases List.mem_cons.mp inside with same | present
        · subst row
          exact bound
        · exact ih tail row present
      · simp only [checkBindings, if_neg bound] at success
        cases success

def validate (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry : Nat)
    (rows : List (Nat × Capability)) : Option (List (Nat × Capability)) :=
  match collect rows [] with
  | none => none
  | some collected =>
      if sortedKeys collected = slots.mergeSort (fun left right => left ≤ right) then
        if checkBindings registry expected families collected = some () then some collected else none
      else none

theorem validation_success (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry : Nat)
    (rows result : List (Nat × Capability))
    (success : validate slots expected families registry rows = some result) :
    collect rows [] = some result ∧
      sortedKeys result = slots.mergeSort (fun left right => left ≤ right) ∧
      checkBindings registry expected families result = some () := by
  cases inserted : collect rows [] with
  | none =>
      simp only [validate, inserted] at success
      cases success
  | some collected =>
      by_cases coverage : sortedKeys collected = slots.mergeSort (fun left right => left ≤ right)
      · by_cases binding : checkBindings registry expected families collected = some ()
        · have same : collected = result := Option.some.inj
            (by simpa only [validate, inserted, if_pos coverage, if_pos binding] using success)
          subst result
          exact ⟨rfl, coverage, binding⟩
        · simp only [validate, inserted, if_pos coverage, if_neg binding] at success
          cases success
      · simp only [validate, inserted, if_neg coverage] at success
        cases success

theorem validation_bound_result (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry : Nat)
    (rows result : List (Nat × Capability))
    (success : validate slots expected families registry rows = some result) :
    BoundRows slots expected result registry := by
  obtain ⟨inserted, coverage, binding⟩ := validation_success slots expected families registry rows result success
  have unique := (collect_success rows [] result (by simp [keys]) inserted).1
  have sorted : (keys result).Perm (slots.mergeSort (fun left right => left ≤ right)) := by
    rw [← coverage]
    exact (List.mergeSort_perm (keys result) (fun left right => left ≤ right)).symm
  refine ⟨unique, sorted.trans (List.mergeSort_perm slots (fun left right => left ≤ right)), ?_⟩
  intro row present
  have checked := check_bindings_success registry expected families result binding row present
  exact ⟨checked.1, checked.2.2⟩

theorem validation_bound_input (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry : Nat)
    (rows result : List (Nat × Capability))
    (success : validate slots expected families registry rows = some result) :
    BoundRows slots expected rows registry := by
  have bound := validation_bound_result slots expected families registry rows result success
  have inserted := (validation_success slots expected families registry rows result success).1
  have retained : result.Perm rows := by
    simpa only [List.append_nil] using
      (collect_success rows [] result (by simp [keys]) inserted).2
  refine ⟨bound.uniqueSlots.perm (retained.map Prod.fst),
    (retained.map Prod.fst).symm.trans bound.exactCoverage, ?_⟩
  intro row present
  exact bound.binds row (retained.mem_iff.mpr present)

theorem every_result_family_checked (slots : List Nat) (expected : Nat → Item)
    (families : Nat → Nat) (registry : Nat) (rows result : List (Nat × Capability))
    (success : validate slots expected families registry rows = some result) :
    ∀ row ∈ result, row.2.item.family = families row.1 := by
  have binding := (validation_success slots expected families registry rows result success).2.2
  intro row inside
  exact (check_bindings_success registry expected families result binding row inside).2.1

theorem every_expected_slot_checked (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry : Nat)
    (rows result : List (Nat × Capability))
    (success : validate slots expected families registry rows = some result) :
    ∀ slot ∈ slots, ∃ capability, (slot, capability) ∈ rows ∧
      capability.registry = registry ∧ capability.item = expected slot :=
  every_expected_slot_bound slots expected rows registry
    (validation_bound_input slots expected families registry rows result success)

theorem adjacent_duplicate_rejected (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry slot : Nat)
    (first second : Capability) (rest : List (Nat × Capability)) :
    validate slots expected families registry ((slot, first) :: (slot, second) :: rest) = none := by
  simp [validate, collect, keys]

theorem wrong_registry_rejected (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry : Nat)
    (rows : List (Nat × Capability)) (row : Nat × Capability)
    (inside : row ∈ rows) (wrong : row.2.registry ≠ registry) :
    ¬ ∃ result, validate slots expected families registry rows = some result := by
  rintro ⟨result, success⟩
  exact wrong_registry_fails_closed slots expected rows registry row inside wrong
    (validation_bound_input slots expected families registry rows result success)

theorem wrong_item_rejected (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat) (registry : Nat)
    (rows : List (Nat × Capability)) (row : Nat × Capability)
    (inside : row ∈ rows) (wrong : row.2.item ≠ expected row.1) :
    ¬ ∃ result, validate slots expected families registry rows = some result := by
  rintro ⟨result, success⟩
  exact wrong_slot_item_fails_closed slots expected rows registry row inside wrong
    (validation_bound_input slots expected families registry rows result success)

end ShielddSecurity.TransferCapabilityRows01

set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.keys
#print axioms ShielddSecurity.TransferCapabilityRows01.keys
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.collect
#print axioms ShielddSecurity.TransferCapabilityRows01.collect
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.collect_success
#print axioms ShielddSecurity.TransferCapabilityRows01.collect_success
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.sortedKeys
#print axioms ShielddSecurity.TransferCapabilityRows01.sortedKeys
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.checkBindings
#print axioms ShielddSecurity.TransferCapabilityRows01.checkBindings
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.check_bindings_success
#print axioms ShielddSecurity.TransferCapabilityRows01.check_bindings_success
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.validate
#print axioms ShielddSecurity.TransferCapabilityRows01.validate
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.validation_success
#print axioms ShielddSecurity.TransferCapabilityRows01.validation_success
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.validation_bound_result
#print axioms ShielddSecurity.TransferCapabilityRows01.validation_bound_result
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.validation_bound_input
#print axioms ShielddSecurity.TransferCapabilityRows01.validation_bound_input
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.every_result_family_checked
#print axioms ShielddSecurity.TransferCapabilityRows01.every_result_family_checked
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.every_expected_slot_checked
#print axioms ShielddSecurity.TransferCapabilityRows01.every_expected_slot_checked
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.adjacent_duplicate_rejected
#print axioms ShielddSecurity.TransferCapabilityRows01.adjacent_duplicate_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.wrong_registry_rejected
#print axioms ShielddSecurity.TransferCapabilityRows01.wrong_registry_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityRows01.wrong_item_rejected
#print axioms ShielddSecurity.TransferCapabilityRows01.wrong_item_rejected
