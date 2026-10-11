import Lean

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferNullifierReaderVector01

/-! Symbolic map/collect and in-place zip model for the pinned nullifier Reader
and contains_nullifiers. A lookup is a verified status at the captured committed
boundary; verification/store correspondence is an explicit upstream interface.
Pending membership is captured from the current disposable block. The model
retains excess vector entries if supplied, matching in-place zip; success of
the actual reader derives full alignment and length instead of assuming them. -/

def Aligned (lookup : Nat → Option Bool) : List Nat → List Bool → Prop
  | [], [] => True
  | key :: rest, flag :: flags => lookup key = some flag ∧ Aligned lookup rest flags
  | _, _ => False

def lookupAll (lookup : Nat → Option Bool) : List Nat → Option (List Bool)
  | [] => some []
  | key :: rest => (lookup key).bind fun flag =>
      (lookupAll lookup rest).map fun flags => flag :: flags

def joinPending (pending : Nat → Bool) : List Nat → List Bool → List Bool
  | [], flags => flags
  | _, [] => []
  | key :: rest, flag :: flags => (flag || pending key) :: joinPending pending rest flags

def zipUnspent : List Nat → List Bool → Bool
  | _ :: rest, flag :: flags => !flag && zipUnspent rest flags
  | _, _ => true

def contains (readerGate : Bool) (lookup : Nat → Option Bool) (pending : Nat → Bool)
    (keys : List Nat) : Option (List Bool) :=
  if readerGate then (lookupAll lookup keys).map (joinPending pending keys) else none

theorem lookup_success_alignment (lookup : Nat → Option Bool) (keys : List Nat)
    (flags : List Bool) (success : lookupAll lookup keys = some flags) :
    Aligned lookup keys flags := by
  induction keys generalizing flags with
  | nil =>
    have same : [] = flags := Option.some.inj success
    subst flags
    trivial
  | cons key rest ih =>
    cases observed : lookup key with
    | none => simp only [lookupAll, observed, Option.bind_none] at success; contradiction
    | some flag =>
      cases later : lookupAll lookup rest with
      | none => simp only [lookupAll, observed, later, Option.bind_some, Option.map_none] at success; contradiction
      | some remaining =>
        have same : flag :: remaining = flags := Option.some.inj
          (by simpa only [lookupAll, observed, later, Option.bind_some, Option.map_some] using success)
        subst flags
        exact ⟨observed, ih remaining later⟩

theorem aligned_length (lookup : Nat → Option Bool) (keys : List Nat) (flags : List Bool)
    (aligned : Aligned lookup keys flags) : flags.length = keys.length := by
  induction keys generalizing flags with
  | nil => cases flags with
    | nil => rfl
    | cons flag rest => cases aligned
  | cons key rest ih => cases flags with
    | nil => cases aligned
    | cons flag remaining => exact congrArg Nat.succ (ih remaining aligned.2)

theorem lookup_success_length (lookup : Nat → Option Bool) (keys : List Nat)
    (flags : List Bool) (success : lookupAll lookup keys = some flags) :
    flags.length = keys.length :=
  aligned_length lookup keys flags (lookup_success_alignment lookup keys flags success)

theorem joinPending_length (pending : Nat → Bool) (keys : List Nat) (flags : List Bool) :
    (joinPending pending keys flags).length = flags.length := by
  induction keys generalizing flags with
  | nil => rfl
  | cons key rest ih => cases flags with
    | nil => rfl
    | cons flag remaining => exact congrArg Nat.succ (ih remaining)

theorem contains_success_actual_vector (readerGate : Bool) (lookup : Nat → Option Bool)
    (pending : Nat → Bool) (keys : List Nat) (flags : List Bool)
    (success : contains readerGate lookup pending keys = some flags) :
    readerGate = true ∧ ∃ durable,
      lookupAll lookup keys = some durable ∧ Aligned lookup keys durable ∧
      flags = joinPending pending keys durable ∧ flags.length = keys.length := by
  cases readerGate with
  | false => simp only [contains, Bool.false_eq_true, if_false] at success; contradiction
  | true =>
    cases observed : lookupAll lookup keys with
    | none => simp only [contains, observed, Bool.true_eq_true, if_true, Option.map_none] at success; contradiction
    | some durable =>
      have same : joinPending pending keys durable = flags := Option.some.inj
        (by simpa only [contains, observed, Bool.true_eq_true, if_true, Option.map_some] using success)
      subst flags
      refine ⟨rfl, durable, rfl, lookup_success_alignment lookup keys durable observed, rfl, ?_⟩
      rw [joinPending_length]
      exact lookup_success_length lookup keys durable observed

theorem aligned_zip_unspent (lookup : Nat → Option Bool) (pending : Nat → Bool)
    (keys : List Nat) (durable : List Bool) (aligned : Aligned lookup keys durable)
    (unspent : zipUnspent keys (joinPending pending keys durable) = true) :
    ∀ key ∈ keys, lookup key = some false ∧ pending key = false := by
  induction keys generalizing durable with
  | nil => intro key inside; cases inside
  | cons head rest ih =>
    cases durable with
    | nil => cases aligned
    | cons flag remaining =>
      have conditions : (flag || pending head) = false ∧
          zipUnspent rest (joinPending pending rest remaining) = true := by
        simpa only [joinPending, zipUnspent, Bool.and_eq_true, Bool.not_eq_true] using unspent
      have booleans := Bool.or_eq_false_iff.mp conditions.1
      intro key inside
      cases List.mem_cons.mp inside with
      | inl same =>
        subst key
        exact ⟨aligned.1.trans (congrArg some booleans.1), booleans.2⟩
      | inr later => exact ih remaining aligned.2 conditions.2 key later

theorem contains_success_unspent (readerGate : Bool) (lookup : Nat → Option Bool)
    (pending : Nat → Bool) (keys : List Nat) (flags : List Bool)
    (success : contains readerGate lookup pending keys = some flags)
    (unspent : zipUnspent keys flags = true) :
    flags.length = keys.length ∧
      ∀ key ∈ keys, lookup key = some false ∧ pending key = false := by
  obtain ⟨_, durable, _, aligned, same, length⟩ :=
    contains_success_actual_vector readerGate lookup pending keys flags success
  rw [same] at unspent
  exact ⟨length, aligned_zip_unspent lookup pending keys durable aligned unspent⟩

theorem lookup_error_refuses_contains (readerGate : Bool) (lookup : Nat → Option Bool)
    (pending : Nat → Bool) (keys : List Nat) (failed : lookupAll lookup keys = none) :
    contains readerGate lookup pending keys = none := by
  cases readerGate <;> simp only [contains, failed, Bool.false_eq_true, Bool.true_eq_true,
    if_false, if_true, Option.map_none]

set_option pp.all true in
#check @Aligned
#print axioms Aligned
set_option pp.all true in
#check @lookupAll
#print axioms lookupAll
set_option pp.all true in
#check @joinPending
#print axioms joinPending
set_option pp.all true in
#check @zipUnspent
#print axioms zipUnspent
set_option pp.all true in
#check @contains
#print axioms contains
set_option pp.all true in
#check @lookup_success_alignment
#print axioms lookup_success_alignment
set_option pp.all true in
#check @aligned_length
#print axioms aligned_length
set_option pp.all true in
#check @lookup_success_length
#print axioms lookup_success_length
set_option pp.all true in
#check @joinPending_length
#print axioms joinPending_length
set_option pp.all true in
#check @contains_success_actual_vector
#print axioms contains_success_actual_vector
set_option pp.all true in
#check @aligned_zip_unspent
#print axioms aligned_zip_unspent
set_option pp.all true in
#check @contains_success_unspent
#print axioms contains_success_unspent
set_option pp.all true in
#check @lookup_error_refuses_contains
#print axioms lookup_error_refuses_contains

end ShielddSecurity.TransferNullifierReaderVector01
