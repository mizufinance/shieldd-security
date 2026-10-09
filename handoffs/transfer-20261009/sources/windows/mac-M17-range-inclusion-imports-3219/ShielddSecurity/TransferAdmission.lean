import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 100000

namespace ShielddSecurity.TransferAdmission

structure Pair where
  userRoot : Nat
  assetRoot : Nat
  deriving DecidableEq

structure Snapshot where
  pair : Pair
  epoch : Nat
  observed : Nat

/-- The source returns for the current pair before history/epoch/time reads.
For a different pair the retained snapshot is exact, within inclusive grace
and in the current freeze epoch. Cryptographic root meaning is separate. -/
def PairAdmitted (current requested : Pair) (history : Option Snapshot)
    (epoch now grace : Nat) : Prop :=
  requested = current ∨ ∃ snapshot, history = some snapshot ∧
    snapshot.pair = requested ∧ snapshot.epoch = epoch ∧
    snapshot.observed ≤ now ∧ 0 < grace ∧ now - snapshot.observed ≤ grace

theorem current_pair_admitted (current : Pair) (history : Option Snapshot)
    (epoch now grace : Nat) : PairAdmitted current current history epoch now grace := by
  exact Or.inl rfl

theorem noncurrent_requires_exact_pair (current requested : Pair) (history : Option Snapshot)
    (epoch now grace : Nat) (different : requested ≠ current)
    (admitted : PairAdmitted current requested history epoch now grace) :
    ∃ snapshot, history = some snapshot ∧ snapshot.pair = requested ∧ snapshot.epoch = epoch := by
  rcases admitted with same | ⟨snapshot, stored, pair, sameEpoch, rest⟩
  · exact False.elim (different same)
  · exact ⟨snapshot, stored, pair, sameEpoch⟩

theorem zero_grace_disables_history (current requested : Pair) (history : Option Snapshot)
    (epoch now : Nat) : PairAdmitted current requested history epoch now 0 ↔ requested = current := by
  constructor
  · intro admitted
    rcases admitted with same | ⟨snapshot, stored, pair, sameEpoch, time, positive, age⟩
    · exact same
    · omega
  · exact Or.inl

theorem epoch_change_does_not_revive_history (current requested : Pair) (snapshot : Snapshot)
    (epoch now grace : Nat) (different : requested ≠ current) (changed : snapshot.epoch ≠ epoch) :
    ¬ PairAdmitted current requested (some snapshot) epoch now grace := by
  intro admitted
  obtain ⟨retained, same, pair, sameEpoch⟩ :=
    noncurrent_requires_exact_pair current requested _ epoch now grace different admitted
  have identity : retained = snapshot := Option.some.inj same.symm
  exact changed (identity ▸ sameEpoch)

theorem grace_endpoint_inclusive (current : Pair) (snapshot : Snapshot) (grace : Nat)
    (positive : 0 < grace) :
    PairAdmitted current snapshot.pair (some snapshot) snapshot.epoch (snapshot.observed + grace) grace := by
  right
  refine ⟨snapshot, rfl, rfl, rfl, ?_, positive, ?_⟩ <;> omega

/-- An unbounded executable savepoint model of the reviewed Transfer write order.
Identifiers stand for already decoded, proof-bound native values. This is not a
Rust refinement, a permanent-bank commit proof, or an SCT-capacity theorem.
Store/SCT/routing/index errors can be inserted as `fail` at any write boundary.
The durable and pending nullifier collections remain distinct. -/
inductive EffectCommand where
  | spend (first second : Nat)
  | note (payload : Nat)
  | volumeNullifier (day nullifier : Nat)
  | volumePayload (payload : Nat)
  | route (entry : Nat)
  | index (transaction : Nat)
  | fail
  deriving DecidableEq

structure EffectState where
  durableNullifiers : List Nat
  pendingNullifiers : List Nat
  notes : List Nat
  volumeNullifiers : List (Nat × Nat)
  volumePayloads : List Nat
  routing : List Nat
  transactionIndex : List Nat
  sourcePresent : Bool
  blockOpen : Bool
  nullifierCapacity : Nat
  deriving DecidableEq

structure TransferEffects where
  spend0 : Nat
  spend1 : Nat
  output0 : Nat
  output1 : Nat
  day : Nat
  volumeNullifier : Nat
  volumePayload : Nat

def SpendReady (state : EffectState) (first second : Nat) : Prop :=
  first ≠ second ∧ first ∉ state.pendingNullifiers ∧ second ∉ state.pendingNullifiers ∧
    first ∉ state.durableNullifiers ∧ second ∉ state.durableNullifiers ∧
    state.sourcePresent = true ∧ state.blockOpen = true ∧
    state.pendingNullifiers.length + 2 ≤ state.nullifierCapacity

instance (state : EffectState) (first second : Nat) : Decidable (SpendReady state first second) :=
  by unfold SpendReady; infer_instance

def effectStep (state : EffectState) : EffectCommand → Option EffectState
  | .spend first second =>
      if SpendReady state first second then
        some { state with pendingNullifiers := state.pendingNullifiers ++ [first, second] }
      else none
  | .note payload => some { state with notes := state.notes ++ [payload] }
  | .volumeNullifier day nullifier =>
      if (day, nullifier) ∈ state.volumeNullifiers then none
      else some { state with volumeNullifiers := state.volumeNullifiers ++ [(day, nullifier)] }
  | .volumePayload payload => some { state with volumePayloads := state.volumePayloads ++ [payload] }
  | .route entry => some { state with routing := state.routing ++ [entry] }
  | .index transaction => some { state with transactionIndex := state.transactionIndex ++ [transaction] }
  | .fail => none

def runEffects (state : EffectState) : List EffectCommand → Option EffectState
  | [] => some state
  | command :: commands => (effectStep state command).bind (fun next => runEffects next commands)

/-- Ordinary has daily-volume effects; FeeFunding has only its two spends and
two outputs. No padding classifier occurs in the persisted-slot program. -/
def transferEffects (ordinary : Bool) (effects : TransferEffects) : List EffectCommand :=
  [.spend effects.spend0 effects.spend1, .note effects.output0, .note effects.output1] ++
    if ordinary then [.volumeNullifier effects.day effects.volumeNullifier,
      .volumePayload effects.volumePayload] else []

def appliedTransfer (state : EffectState) (ordinary : Bool) (effects : TransferEffects) : EffectState :=
  { state with
    pendingNullifiers := state.pendingNullifiers ++ [effects.spend0, effects.spend1]
    notes := state.notes ++ [effects.output0, effects.output1]
    volumeNullifiers := state.volumeNullifiers ++
      (if ordinary then [(effects.day, effects.volumeNullifier)] else [])
    volumePayloads := state.volumePayloads ++ (if ordinary then [effects.volumePayload] else []) }

/-- The outer savepoint applies only a successful result, including routing and
index writes. A partial working delta is never applied after an error. -/
def applySavepoint (base : EffectState) (result : Option EffectState) : EffectState :=
  match result with
  | none => base
  | some working => working

def executeTransaction (base : EffectState) (commands : List EffectCommand) : EffectState :=
  applySavepoint base (runEffects base commands)

theorem duplicate_before_mutation (state : EffectState) (nullifier : Nat) :
    effectStep state (.spend nullifier nullifier) = none := by
  simp [effectStep, SpendReady]

theorem pending_respend_before_mutation (state : EffectState) (first second : Nat)
    (spent : first ∈ state.pendingNullifiers) : effectStep state (.spend first second) = none := by
  simp [effectStep, SpendReady, spent]

theorem durable_respend_before_mutation (state : EffectState) (first second : Nat)
    (spent : second ∈ state.durableNullifiers) : effectStep state (.spend first second) = none := by
  simp [effectStep, SpendReady, spent]

theorem exact_two_spends_staged (state : EffectState) (first second : Nat)
    (ready : SpendReady state first second) :
    effectStep state (.spend first second) =
      some { state with pendingNullifiers := state.pendingNullifiers ++ [first, second] } := by
  simp [effectStep, ready]

theorem exact_transfer_effects (state : EffectState) (ordinary : Bool) (effects : TransferEffects)
    (ready : SpendReady state effects.spend0 effects.spend1)
    (volumeFresh : ordinary = true → (effects.day, effects.volumeNullifier) ∉ state.volumeNullifiers) :
    runEffects state (transferEffects ordinary effects) = some (appliedTransfer state ordinary effects) := by
  cases ordinary with
  | false => simp [runEffects, transferEffects, effectStep, ready, appliedTransfer, List.append_assoc]
  | true =>
      have fresh := volumeFresh rfl
      simp [runEffects, transferEffects, effectStep, ready, fresh, appliedTransfer, List.append_assoc]

/-- Volume replay admission happens before ordinary effects; the write itself
also rechecks the day/nullifier pair. FeeFunding bypasses this daily check.
Exact capability, paired-root and timestamp checks are separate admission joins. -/
def runVolumeCheckedTransfer (state : EffectState) (ordinary : Bool) (effects : TransferEffects) :
    Option EffectState :=
  if ordinary = true ∧ (effects.day, effects.volumeNullifier) ∈ state.volumeNullifiers then none
  else runEffects state (transferEffects ordinary effects)

theorem ordinary_volume_replay_before_mutation (state : EffectState) (effects : TransferEffects)
    (spent : (effects.day, effects.volumeNullifier) ∈ state.volumeNullifiers) :
    runVolumeCheckedTransfer state true effects = none := by
  simp [runVolumeCheckedTransfer, spent]

theorem fee_funding_bypasses_volume_replay (state : EffectState) (effects : TransferEffects) :
    runVolumeCheckedTransfer state false effects = runEffects state (transferEffects false effects) := by
  simp [runVolumeCheckedTransfer]

theorem ordered_outputs_persist (state : EffectState) (ordinary : Bool) (effects : TransferEffects) :
    (appliedTransfer state ordinary effects).notes = state.notes ++ [effects.output0, effects.output1] := by
  rfl

/-- The second slot is persisted even when its circuit witness is padding.
The witness classification has no influence on this fixed-shape write list. -/
theorem padding_slot_persisted (state : EffectState) (ordinary : Bool) (effects : TransferEffects) :
    (appliedTransfer state ordinary effects).pendingNullifiers =
      state.pendingNullifiers ++ [effects.spend0, effects.spend1] := by
  rfl

theorem ordinary_volume_effects (state : EffectState) (effects : TransferEffects) :
    (appliedTransfer state true effects).volumeNullifiers =
      state.volumeNullifiers ++ [(effects.day, effects.volumeNullifier)] ∧
    (appliedTransfer state true effects).volumePayloads = state.volumePayloads ++ [effects.volumePayload] := by
  exact ⟨rfl, rfl⟩

theorem fee_funding_no_volume_effects (state : EffectState) (effects : TransferEffects) :
    (appliedTransfer state false effects).volumeNullifiers = state.volumeNullifiers ∧
    (appliedTransfer state false effects).volumePayloads = state.volumePayloads := by
  simp [appliedTransfer]

theorem duplicate_volume_fails (state : EffectState) (day nullifier : Nat)
    (spent : (day, nullifier) ∈ state.volumeNullifiers) :
    effectStep state (.volumeNullifier day nullifier) = none := by
  simp [effectStep, spent]

theorem run_effects_append (state : EffectState) (first second : List EffectCommand) :
    runEffects state (first ++ second) = (runEffects state first).bind (fun next => runEffects next second) := by
  induction first generalizing state with
  | nil => rfl
  | cons command commands ih =>
      cases step : effectStep state command with
      | none => simp [runEffects, step]
      | some next => simpa [runEffects, step] using ih next

theorem fault_after_arbitrary_prefix (state : EffectState) (earlierCommands suffix : List EffectCommand) :
    runEffects state (earlierCommands ++ .fail :: suffix) = none := by
  rw [run_effects_append]
  cases runEffects state earlierCommands <;> rfl

theorem failed_transaction_restores_snapshot (base : EffectState) (commands : List EffectCommand)
    (failed : runEffects base commands = none) : executeTransaction base commands = base := by
  simp [executeTransaction, failed, applySavepoint]

theorem arbitrary_write_boundary_rollback (base : EffectState) (earlierCommands suffix : List EffectCommand) :
    executeTransaction base (earlierCommands ++ .fail :: suffix) = base := by
  exact failed_transaction_restores_snapshot base _ (fault_after_arbitrary_prefix base earlierCommands suffix)

theorem routing_and_index_rollback (base : EffectState) (earlierCommands suffix : List EffectCommand)
    (route transaction : Nat) :
    executeTransaction base (earlierCommands ++ [.route route, .index transaction, .fail] ++ suffix) = base := by
  apply failed_transaction_restores_snapshot
  rw [run_effects_append, run_effects_append]
  cases runEffects base earlierCommands <;> rfl

theorem successful_transaction_applies_delta (base working : EffectState) (commands : List EffectCommand)
    (success : runEffects base commands = some working) : executeTransaction base commands = working := by
  simp [executeTransaction, success, applySavepoint]

def bodyAndFeeEffects (body : List EffectCommand) (fee : Option TransferEffects) : List EffectCommand :=
  body ++ match fee with
    | none => []
    | some effects => transferEffects false effects

theorem fee_funding_after_body (state : EffectState) (body : List EffectCommand) (fee : TransferEffects) :
    runEffects state (bodyAndFeeEffects body (some fee)) =
      (runEffects state body).bind (fun afterBody => runEffects afterBody (transferEffects false fee)) := by
  exact run_effects_append state body (transferEffects false fee)

theorem failed_body_never_executes_fee (state : EffectState) (body : List EffectCommand) (fee : TransferEffects)
    (failed : runEffects state body = none) :
    runEffects state (bodyAndFeeEffects body (some fee)) = none := by
  rw [fee_funding_after_body, failed]
  rfl

set_option pp.all true in
#check @duplicate_before_mutation
#print axioms duplicate_before_mutation
set_option pp.all true in
#check @pending_respend_before_mutation
#print axioms pending_respend_before_mutation
set_option pp.all true in
#check @durable_respend_before_mutation
#print axioms durable_respend_before_mutation
set_option pp.all true in
#check @exact_two_spends_staged
#print axioms exact_two_spends_staged
set_option pp.all true in
#check @exact_transfer_effects
#print axioms exact_transfer_effects
set_option pp.all true in
#check @ordinary_volume_replay_before_mutation
#print axioms ordinary_volume_replay_before_mutation
set_option pp.all true in
#check @fee_funding_bypasses_volume_replay
#print axioms fee_funding_bypasses_volume_replay
set_option pp.all true in
#check @ordered_outputs_persist
#print axioms ordered_outputs_persist
set_option pp.all true in
#check @padding_slot_persisted
#print axioms padding_slot_persisted
set_option pp.all true in
#check @ordinary_volume_effects
#print axioms ordinary_volume_effects
set_option pp.all true in
#check @fee_funding_no_volume_effects
#print axioms fee_funding_no_volume_effects
set_option pp.all true in
#check @duplicate_volume_fails
#print axioms duplicate_volume_fails
set_option pp.all true in
#check @run_effects_append
#print axioms run_effects_append
set_option pp.all true in
#check @fault_after_arbitrary_prefix
#print axioms fault_after_arbitrary_prefix
set_option pp.all true in
#check @failed_transaction_restores_snapshot
#print axioms failed_transaction_restores_snapshot
set_option pp.all true in
#check @arbitrary_write_boundary_rollback
#print axioms arbitrary_write_boundary_rollback
set_option pp.all true in
#check @routing_and_index_rollback
#print axioms routing_and_index_rollback
set_option pp.all true in
#check @successful_transaction_applies_delta
#print axioms successful_transaction_applies_delta
set_option pp.all true in
#check @fee_funding_after_body
#print axioms fee_funding_after_body
set_option pp.all true in
#check @failed_body_never_executes_fee
#print axioms failed_body_never_executes_fee
set_option pp.all true in
#check @current_pair_admitted
#print axioms current_pair_admitted
set_option pp.all true in
#check @noncurrent_requires_exact_pair
#print axioms noncurrent_requires_exact_pair
set_option pp.all true in
#check @zero_grace_disables_history
#print axioms zero_grace_disables_history
set_option pp.all true in
#check @epoch_change_does_not_revive_history
#print axioms epoch_change_does_not_revive_history
set_option pp.all true in
#check @grace_endpoint_inclusive
#print axioms grace_endpoint_inclusive

end ShielddSecurity.TransferAdmission
