import ShielddSecurity.TransferDeferredCountWalk01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferDeferredCountFlush01
open TransferStateDelta TransferIndexWriterModel01 TransferDeferredCountWalk01

/-! Successful concrete deferred flush derives the count, queue consumption
and original V/object preservation. The parent may contain earlier delivered
effects. No per-callback frame or desired poststate is assumed. Actual Rust
ownership, source height/byte/key/proof/native/Host/durability remain interfaces. -/

theorem successful_step_preserves_non_index_effects {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (action : A) (parent : State O) (cache nextCache : Cache O E)
    (success : queueWriter keys convert available parent height cache action = .ok nextCache) :
    nextCache.verifiable = cache.verifiable ∧ nextCache.objects = cache.objects ∧ nextCache.events = cache.events := by
  cases inspected : inspect keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert available) height action ⟨parent, cache⟩ with
  | error error => simp only [queueWriter, inspected] at success; contradiction
  | ok witness =>
    have same : writeIndex keys TransferIndexCountCodec01.codec height witness cache = nextCache :=
      Except.ok.inj (by simpa only [queueWriter, inspected] using success)
    rw [← same]
    exact writeIndex_frames keys TransferIndexCountCodec01.codec height witness cache

theorem successful_walk_preserves_non_index_effects {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (actions : List A) (cache finalCache : Cache O E)
    (success : TransferDeferredQueueSourceModel01.walk (queueWriter keys convert available parent)
      height cache actions = .ok finalCache) :
    finalCache.verifiable = cache.verifiable ∧ finalCache.objects = cache.objects ∧ finalCache.events = cache.events := by
  induction actions generalizing cache with
  | nil =>
    have same : cache = finalCache := Except.ok.inj success
    subst finalCache
    exact ⟨rfl, rfl, rfl⟩
  | cons action rest ih =>
    cases step : queueWriter keys convert available parent height cache action with
    | error error => simp only [TransferDeferredQueueSourceModel01.walk, step] at success; contradiction
    | ok nextCache =>
      have suffix : TransferDeferredQueueSourceModel01.walk (queueWriter keys convert available parent)
          height nextCache rest = .ok finalCache := by
        simpa only [TransferDeferredQueueSourceModel01.walk, step] using success
      have first := successful_step_preserves_non_index_effects keys convert available height action parent cache nextCache step
      have later := ih nextCache suffix
      exact ⟨later.1.trans first.1, later.2.1.trans first.2.1, later.2.2.trans first.2.2⟩

theorem successful_nonempty_flush_derives_count_queue_and_effects {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (actions : List A) (initial : Ordinal)
    (nonempty : actions ≠ [])
    (observed : countObservation TransferIndexCountCodec01.codec (parent.nonverifiable (keys.count height)) = some initial)
    (success : (TransferDeferredQueueSourceModel01.flush (queueWriter (E := E) keys convert available parent)
      true true (some height) parent actions).error = none) :
    let result := TransferDeferredQueueSourceModel01.flush (queueWriter (E := E) keys convert available parent)
      true true (some height) parent actions
    ∃ final : Ordinal,
      countObservation TransferIndexCountCodec01.codec (result.parent.nonverifiable (keys.count height)) = some final ∧
      final.val = initial.val + actions.length ∧ initial.val + actions.length < 2 ^ 64 ∧
      result.parent.verifiable = parent.verifiable ∧ result.parent.objects = parent.objects ∧
      result.queued = [] ∧ result.events = [] := by
  dsimp only
  rw [TransferDeferredQueueSourceModel01.post_take_dispatch _ height parent actions nonempty] at success ⊢
  cases walked : TransferDeferredQueueSourceModel01.walk (queueWriter (E := E) keys convert available parent)
      height empty actions with
  | error error => simp only [walked, TransferDeferredQueueSourceModel01.refused] at success; contradiction
  | ok cache =>
    simp only [walked]
    have initialRead : countObservation TransferIndexCountCodec01.codec
        ((applyCache parent (empty (E := E))).nonverifiable (keys.count height)) = some initial := by
      rw [apply_empty]
      exact observed
    obtain ⟨final, decoded, increased⟩ := successful_walk_derives_exact_count_increase keys convert available height parent
      actions empty cache initial initialRead walked
    have frames := successful_walk_preserves_non_index_effects keys convert available height parent actions empty cache walked
    refine ⟨final, decoded, increased, ?_, ?_, ?_, rfl, ?_⟩
    · rw [← increased]
      exact final.isLt
    · change overlay parent.verifiable cache.verifiable = parent.verifiable
      rw [frames.1]
      rfl
    · change overlay parent.objects cache.objects = parent.objects
      rw [frames.2.1]
      rfl
    · exact frames.2.2

set_option pp.all true in
#check @successful_step_preserves_non_index_effects
#print axioms successful_step_preserves_non_index_effects
set_option pp.all true in
#check @successful_walk_preserves_non_index_effects
#print axioms successful_walk_preserves_non_index_effects
set_option pp.all true in
#check @successful_nonempty_flush_derives_count_queue_and_effects
#print axioms successful_nonempty_flush_derives_count_queue_and_effects
end ShielddSecurity.TransferDeferredCountFlush01
