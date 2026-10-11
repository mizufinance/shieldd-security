import ShielddSecurity.TransferRawEffectsSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCapabilitySource01

open TransferStateDelta TransferRawStateProgram01

/-! Stateless re-extraction and exact capability comparison precede every raw
effect. Item denotes the complete decoded Verification value, not a digest.
The extractor's anchor/shape/context/auth/length/public-statement behavior and
the validated token's proof/state provenance remain explicit upstream joins.
This wrapper derives matching from its comparison rather than supplying a
desired exactMatched boolean. It uses the actual two runtime proof contexts. -/

inductive ProofContext where
  | ordinary | feeFunding

def isOrdinary : ProofContext → Bool
  | .ordinary => true
  | .feeFunding => false

structure Validated (I : Type) where
  item : I
  context : ProofContext

inductive Error (K X : Type) where
  | extraction (error : K) | mismatch | raw (error : TransferRawEffectsSource01.EffectError X)

def liftRaw {O E K X : Type} (returned : Outcome O E (TransferRawEffectsSource01.EffectError X)) :
    Outcome O E (Error K X) :=
  ⟨returned.cache, match returned.result with
    | .error error => .error (.raw error)
    | .ok () => .ok ()⟩

def execute {O E K X A I : Type} [DecidableEq I]
    (raw : TransferRawEffectsSource01.Backend O E X)
    (extract : A → ProofContext → Except K I) (inputs outputs : A → List Nat)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (action : A) (token : Validated I)
    (child : Delta O E) : Outcome O E (Error K X) :=
  match extract action token.context with
  | .error error => ⟨child.cache, .error (.extraction error)⟩
  | .ok item =>
      if item = token.item then liftRaw
        (TransferRawEffectsSource01.executeTransfer raw wordMax capacity pendingKey entryKey dayKey
          true (isOrdinary token.context) child (inputs action) (outputs action))
      else ⟨child.cache, .error .mismatch⟩

theorem extraction_failure_precedes_effects {O E K X A I : Type} [DecidableEq I]
    (raw : TransferRawEffectsSource01.Backend O E X)
    (extract : A → ProofContext → Except K I) (inputs outputs : A → List Nat)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (action : A) (token : Validated I)
    (child : Delta O E) (error : K) (failed : extract action token.context = .error error) :
    execute raw extract inputs outputs wordMax capacity pendingKey entryKey dayKey action token child =
      ⟨child.cache, .error (.extraction error)⟩ := by
  simp only [execute, failed]

theorem different_item_precedes_effects {O E K X A I : Type} [DecidableEq I]
    (raw : TransferRawEffectsSource01.Backend O E X)
    (extract : A → ProofContext → Except K I) (inputs outputs : A → List Nat)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (action : A) (token : Validated I)
    (child : Delta O E) (item : I) (observed : extract action token.context = .ok item)
    (different : item ≠ token.item) :
    execute raw extract inputs outputs wordMax capacity pendingKey entryKey dayKey action token child =
      ⟨child.cache, .error .mismatch⟩ := by
  simp only [execute, observed, if_neg different]

theorem exact_rebinding_dispatches_projected_action {O E K X A I : Type} [DecidableEq I]
    (raw : TransferRawEffectsSource01.Backend O E X)
    (extract : A → ProofContext → Except K I) (inputs outputs : A → List Nat)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (action : A) (token : Validated I)
    (child : Delta O E) (observed : extract action token.context = .ok token.item) :
    execute raw extract inputs outputs wordMax capacity pendingKey entryKey dayKey action token child =
      liftRaw (TransferRawEffectsSource01.executeTransfer raw wordMax capacity pendingKey entryKey dayKey
        true (isOrdinary token.context) child (inputs action) (outputs action)) := by
  simp only [execute, observed, ite_true]

theorem successful_execution_derives_exact_reextraction {O E K X A I : Type} [DecidableEq I]
    (raw : TransferRawEffectsSource01.Backend O E X)
    (extract : A → ProofContext → Except K I) (inputs outputs : A → List Nat)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (action : A) (token : Validated I)
    (child : Delta O E)
    (success : (execute raw extract inputs outputs wordMax capacity pendingKey entryKey dayKey action token child).result = .ok ()) :
    extract action token.context = .ok token.item := by
  cases observed : extract action token.context with
  | error error => simp [execute, observed] at success
  | ok item =>
      by_cases equal : item = token.item
      · simpa only [equal] using observed
      · simp [execute, observed, equal] at success

theorem bound_ordinary_late_conflict_retains_earlier_cache {O E K X A I : Type} [DecidableEq I]
    (raw : TransferRawEffectsSource01.Backend O E X)
    (extract : A → ProofContext → Except K I) (inputs outputs : A → List Nat)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (action : A) (item : I)
    (child : Delta O E) (middle : Cache O E) (sourceHasId : Bool)
    (observed : extract action .ordinary = .ok item)
    (reshaped : TransferRawEffectsSource01.reshape raw wordMax capacity pendingKey child (inputs action) (outputs action) = ⟨middle, .ok ()⟩)
    (source : raw.currentSource {child with cache := middle} = some sourceHasId)
    (spent : raw.volumePresent {child with cache := middle} = some true) :
    execute raw extract inputs outputs wordMax capacity pendingKey entryKey dayKey action ⟨item, .ordinary⟩ child =
      ⟨middle, .error (.raw .volumeSpent)⟩ := by
  rw [exact_rebinding_dispatches_projected_action raw extract inputs outputs wordMax capacity pendingKey entryKey dayKey
    action ⟨item, .ordinary⟩ child observed]
  rw [isOrdinary, TransferRawEffectsSource01.actual_late_volume_conflict_keeps_earlier_raw_cache raw
    wordMax capacity pendingKey entryKey dayKey child (inputs action) (outputs action) middle sourceHasId reshaped source spent]
  rfl

set_option pp.all true in
#check @ProofContext
#print axioms ProofContext
set_option pp.all true in
#check @isOrdinary
#print axioms isOrdinary
set_option pp.all true in
#check @Validated
#print axioms Validated
set_option pp.all true in
#check @Error
#print axioms Error
set_option pp.all true in
#check @liftRaw
#print axioms liftRaw
set_option pp.all true in
#check @execute
#print axioms execute
set_option pp.all true in
#check @extraction_failure_precedes_effects
#print axioms extraction_failure_precedes_effects
set_option pp.all true in
#check @different_item_precedes_effects
#print axioms different_item_precedes_effects
set_option pp.all true in
#check @exact_rebinding_dispatches_projected_action
#print axioms exact_rebinding_dispatches_projected_action
set_option pp.all true in
#check @successful_execution_derives_exact_reextraction
#print axioms successful_execution_derives_exact_reextraction
set_option pp.all true in
#check @bound_ordinary_late_conflict_retains_earlier_cache
#print axioms bound_ordinary_late_conflict_retains_earlier_cache

end ShielddSecurity.TransferCapabilitySource01
