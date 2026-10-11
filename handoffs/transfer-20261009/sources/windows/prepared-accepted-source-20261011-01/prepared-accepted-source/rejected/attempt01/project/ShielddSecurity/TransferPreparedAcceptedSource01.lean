import ShielddSecurity.TransferBlockSealJoin01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPreparedAcceptedSource01
open TransferStateDelta
open TransferReadback (Boundary Store)
open TransferNullifierBatchSource01 (Pending uniqueLoop)
open TransferBlockPendingSequence01 (Request parentPending allInputs)
open TransferNullifierConsensusLimits01 (blockCapacity)

/-! Store::prepare retains the original accepted order in its transition.
The source prefix checks readiness, partition health, intent absence, length,
set uniqueness, current roots/boundary and checked consecutive height. Its
partition preparation (key partitioning/sorting/collision tests, session reads,
finish, witnesses and verify_insertions) is an explicit fallible interface.
The assembled next roots are the observed interface output, never assumed to
equal a requested poststate. No persistence, witness validity, native vector/
set/getter correspondence, owner scheduling or complete Host certification. -/

structure Backend where
  store : Store
  intentPending : Bool
  sessions : Boundary → List Nat → Option (List Nat)

structure Prepared where
  previous : Boundary
  next : Boundary
  accepted : List Nat

def Consecutive (previous : Boundary) (height : Fin (2 ^ 64)) : Bool :=
  match previous.height with
  | none => decide (height.val = 0)
  | some earlier => decide (earlier + 1 < 2 ^ 64 ∧ earlier + 1 = height.val)

def Gate (backend : Backend) (previous : Boundary) (height : Fin (2 ^ 64)) (accepted : List Nat) : Prop :=
  backend.store.ready = true ∧ backend.store.healthy = true ∧ backend.intentPending = false ∧
    accepted.length ≤ blockCapacity ∧ uniqueLoop [] accepted = true ∧
    backend.store.actualRoots = previous.roots ∧ backend.store.boundary = some previous ∧
    Consecutive previous height = true

def prepare (backend : Backend) (previous : Boundary) (height : Fin (2 ^ 64)) (blockId accepted : List Nat) : Option Prepared :=
  if Gate backend previous height accepted then
    (backend.sessions previous accepted).map fun observedRoots =>
      ⟨previous, ⟨some height.val, blockId, observedRoots⟩, accepted⟩
  else none

theorem nodup_fresh_accepts_unique_loop (seen keys : List Nat) (nodup : keys.Nodup)
    (fresh : ∀ key ∈ keys, key ∉ seen) : uniqueLoop seen keys = true := by
  induction keys generalizing seen with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨headAbsent, tailNodup⟩ := List.nodup_cons.mp nodup
    have absent : seen.contains head = false := by simpa using fresh head (by simp)
    have tailFresh : ∀ key ∈ rest, key ∉ head :: seen := by
      intro key inside held
      cases List.mem_cons.mp held with
      | inl same => subst key; exact headAbsent inside
      | inr inSeen => exact fresh key (List.mem_cons_of_mem head inside) inSeen
    simpa only [uniqueLoop, absent, Bool.false_eq_true, if_false] using ih (head :: seen) tailNodup tailFresh

theorem successful_prepare_derives_gate_and_exact_transition (backend : Backend) (previous : Boundary)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) (result : Prepared)
    (success : prepare backend previous height blockId accepted = some result) :
    Gate backend previous height accepted ∧ accepted.Nodup ∧
      ∃ observedRoots, backend.sessions previous accepted = some observedRoots ∧
        result.previous = previous ∧ result.next.height = some height.val ∧ result.next.blockId = blockId ∧
        result.next.roots = observedRoots ∧ result.accepted = accepted := by
  by_cases gate : Gate backend previous height accepted
  · cases observed : backend.sessions previous accepted with
    | none => simp only [prepare, if_pos gate, observed, Option.map_none] at success; contradiction
    | some roots =>
      have same : (⟨previous, ⟨some height.val, blockId, roots⟩, accepted⟩ : Prepared) = result := by
        exact Option.some.inj (by simpa only [prepare, if_pos gate, observed, Option.map_some] using success)
      subst result
      exact ⟨gate, (TransferPendingSetInvariant01.unique_loop_derives_nodup_and_fresh [] accepted gate.2.2.2.2.1).1,
        roots, observed, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [prepare, if_neg gate] at success; contradiction

theorem capacity_or_duplicate_refuses_before_sessions (backend : Backend) (previous : Boundary)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat)
    (invalid : blockCapacity < accepted.length ∨ ¬ accepted.Nodup) :
    prepare backend previous height blockId accepted = none := by
  have denied : ¬ Gate backend previous height accepted := by
    intro gate
    cases invalid with
    | inl oversized => exact (Nat.not_le_of_gt oversized) gate.2.2.2.1
    | inr duplicate => exact duplicate (TransferPendingSetInvariant01.unique_loop_derives_nodup_and_fresh [] accepted gate.2.2.2.2.1).1
  simp only [prepare, if_neg denied]

theorem whole_block_frozen_inputs_pass_capacity_and_duplicate_gates {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final) :
    let output := TransferPendingSealSource01.sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
    let accepted := (parentPending decode project (applyCache final.1 output.cache)).ordered
    accepted = allInputs requests ∧ accepted.Nodup ∧ accepted.length ≤ blockCapacity ∧ uniqueLoop [] accepted = true := by
  dsimp only
  have sealed := TransferBlockSealJoin01.successful_block_seals_exact_global_inputs_once_and_refuses_later_staging encode decode roundtrip
    project injection requests parent queued final emptyStart success
  have exactInputs := sealed.2.2.2.2.1
  rw [exactInputs]
  have nodup := sealed.2.2.2.2.2.1
  exact ⟨rfl, nodup, sealed.2.2.2.2.2.2.1, nodup_fresh_accepts_unique_loop [] (allInputs requests) nodup (by simp)⟩

theorem whole_block_prepare_assembles_exact_observed_transition {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final)
    (backend : Backend) (previous : Boundary) (height : Fin (2 ^ 64)) (blockId observedRoots : List Nat)
    (ready : backend.store.ready = true) (healthy : backend.store.healthy = true) (noIntent : backend.intentPending = false)
    (roots : backend.store.actualRoots = previous.roots) (boundary : backend.store.boundary = some previous)
    (consecutive : Consecutive previous height = true) (sessions : backend.sessions previous (allInputs requests) = some observedRoots) :
    let output := TransferPendingSealSource01.sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
    let accepted := (parentPending decode project (applyCache final.1 output.cache)).ordered
    prepare backend previous height blockId accepted = some ⟨previous, ⟨some height.val, blockId, observedRoots⟩, allInputs requests⟩ := by
  dsimp only
  have derived := whole_block_frozen_inputs_pass_capacity_and_duplicate_gates encode decode roundtrip project injection
    requests parent queued final emptyStart success
  rw [derived.1]
  have gate : Gate backend previous height (allInputs requests) :=
    ⟨ready, healthy, noIntent, by simpa only [derived.1] using derived.2.2.1,
      by simpa only [derived.1] using derived.2.2.2, roots, boundary, consecutive⟩
  simp only [prepare, if_pos gate, sessions, Option.map_some]

set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @Prepared
#print axioms Prepared
set_option pp.all true in
#check @Consecutive
#print axioms Consecutive
set_option pp.all true in
#check @Gate
#print axioms Gate
set_option pp.all true in
#check @prepare
#print axioms prepare
set_option pp.all true in
#check @nodup_fresh_accepts_unique_loop
#print axioms nodup_fresh_accepts_unique_loop
set_option pp.all true in
#check @successful_prepare_derives_gate_and_exact_transition
#print axioms successful_prepare_derives_gate_and_exact_transition
set_option pp.all true in
#check @capacity_or_duplicate_refuses_before_sessions
#print axioms capacity_or_duplicate_refuses_before_sessions
set_option pp.all true in
#check @whole_block_frozen_inputs_pass_capacity_and_duplicate_gates
#print axioms whole_block_frozen_inputs_pass_capacity_and_duplicate_gates
set_option pp.all true in
#check @whole_block_prepare_assembles_exact_observed_transition
#print axioms whole_block_prepare_assembles_exact_observed_transition
end ShielddSecurity.TransferPreparedAcceptedSource01
