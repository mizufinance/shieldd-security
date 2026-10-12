import ShielddSecurity.TransferOrdinaryDecodableIndex01
import ShielddSecurity.TransferDeferredQueueSourceModel01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferDeferredCountWalk01
open TransferStateDelta TransferIndexWriterModel01
open TransferOrdinaryIndexReadSource01

/-! An arbitrary successful deferred index walk derives its count increase
through actual modeled overlay reads and concrete u64 encoding. The original
count observation is an input-state premise. No per-step increment, successful
callback poststate or final counter is assumed. Rust, byte/key/ownership/native
and durable-store correspondence remain separate interfaces. -/

def queueWriter {O E A : Type} (keys : Keys) (convert : A → Option Encoded)
    (available : Delta O E → Nat → Bool) (parent : State O) :
    TransferDeferredQueueSourceModel01.IndexWriter O E A IndexError :=
  fun height cache action => match inspect keys TransferIndexCountCodec01.codec
      (installReads convert available) height action ⟨parent, cache⟩ with
    | .error error => .error error
    | .ok witness => .ok (writeIndex keys TransferIndexCountCodec01.codec height witness cache)

theorem successful_step_derives_count_increment {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (action : A) (parent : State O) (cache nextCache : Cache O E) (initial : Ordinal)
    (observed : countObservation TransferIndexCountCodec01.codec
      ((applyCache parent cache).nonverifiable (keys.count height)) = some initial)
    (success : queueWriter keys convert available parent height cache action = .ok nextCache) :
    ∃ next : Ordinal, countObservation TransferIndexCountCodec01.codec
      ((applyCache parent nextCache).nonverifiable (keys.count height)) = some next ∧
      next.val = initial.val + 1 := by
  cases inspected : inspect keys TransferIndexCountCodec01.codec (installReads convert available)
      height action ⟨parent, cache⟩ with
  | error error => simp only [queueWriter, inspected] at success; contradiction
  | ok witness =>
    have cacheEqual : writeIndex keys TransferIndexCountCodec01.codec height witness cache = nextCache :=
      Except.ok.inj (by simpa only [queueWriter, inspected] using success)
    have current := TransferOrdinaryIndexCountSource01.successful_inspection_derives_current_count
      keys TransferIndexCountCodec01.codec convert available height action ⟨parent, cache⟩ witness inspected
    have ordinalEqual : witness.ordinal = initial := Option.some.inj (current.2.1.symm.trans observed)
    have increment := TransferIndexInspectionFacts01.inspect_success_checked_increment
      keys TransferIndexCountCodec01.codec (installReads convert available) height action ⟨parent, cache⟩ witness inspected
    refine ⟨witness.next, ?_, ?_⟩
    · rw [← cacheEqual]
      change countObservation TransferIndexCountCodec01.codec (overlay parent.nonverifiable
        (writeIndex keys TransferIndexCountCodec01.codec height witness cache).nonverifiable (keys.count height)) = some witness.next
      simp only [overlay, writeIndex_count]
      exact TransferIndexCountCodec01.codec_roundtrip witness.next
    · simpa only [ordinalEqual] using increment.1

theorem successful_walk_derives_exact_count_increase {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (actions : List A) (cache finalCache : Cache O E) (initial : Ordinal)
    (observed : countObservation TransferIndexCountCodec01.codec
      ((applyCache parent cache).nonverifiable (keys.count height)) = some initial)
    (success : TransferDeferredQueueSourceModel01.walk (queueWriter keys convert available parent)
      height cache actions = .ok finalCache) :
    ∃ final : Ordinal, countObservation TransferIndexCountCodec01.codec
      ((applyCache parent finalCache).nonverifiable (keys.count height)) = some final ∧
      final.val = initial.val + actions.length := by
  induction actions generalizing cache initial with
  | nil =>
    have same : cache = finalCache := Except.ok.inj success
    subst finalCache
    exact ⟨initial, observed, rfl⟩
  | cons action rest ih =>
    cases step : queueWriter keys convert available parent height cache action with
    | error error => simp only [TransferDeferredQueueSourceModel01.walk, step] at success; contradiction
    | ok nextCache =>
      have suffix : TransferDeferredQueueSourceModel01.walk (queueWriter keys convert available parent)
          height nextCache rest = .ok finalCache := by
        simpa only [TransferDeferredQueueSourceModel01.walk, step] using success
      obtain ⟨next, current, increment⟩ := successful_step_derives_count_increment keys convert available height action
        parent cache nextCache initial observed step
      obtain ⟨final, decoded, increased⟩ := ih nextCache next current suffix
      refine ⟨final, decoded, ?_⟩
      rw [increased, increment, List.length_cons]
      omega

theorem successful_walk_cannot_wrap_u64 {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (actions : List A) (cache finalCache : Cache O E) (initial : Ordinal)
    (observed : countObservation TransferIndexCountCodec01.codec
      ((applyCache parent cache).nonverifiable (keys.count height)) = some initial)
    (success : TransferDeferredQueueSourceModel01.walk (queueWriter keys convert available parent)
      height cache actions = .ok finalCache) :
    initial.val + actions.length < 2 ^ 64 := by
  obtain ⟨final, _, increased⟩ := successful_walk_derives_exact_count_increase keys convert available height parent actions
    cache finalCache initial observed success
  rw [← increased]
  exact final.isLt

set_option pp.all true in
#check @queueWriter
#print axioms queueWriter
set_option pp.all true in
#check @successful_step_derives_count_increment
#print axioms successful_step_derives_count_increment
set_option pp.all true in
#check @successful_walk_derives_exact_count_increase
#print axioms successful_walk_derives_exact_count_increase
set_option pp.all true in
#check @successful_walk_cannot_wrap_u64
#print axioms successful_walk_cannot_wrap_u64
end ShielddSecurity.TransferDeferredCountWalk01
