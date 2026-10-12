import ShielddSecurity.TransferWholeReaderRefusal01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPendingSetInvariant01
open TransferStateDelta TransferNullifierBatchSource01

/-! Small symbolic set/list lemmas for the pinned Open pending-block append.
Coherence relates the membership set to the ordered vector. The successful
primitive derives new uniqueness, freshness and capacity; no desired next
invariant is supplied. Typed collection/getter/Clone/native correspondence
remains explicit. No native or executed negative-control credit. -/

def Coherent (pending : Pending) : Prop :=
  ∀ key, pending.membership key = pending.ordered.contains key

def Invariant (capacity : Nat) (pending : Pending) : Prop :=
  Coherent pending ∧ pending.ordered.Nodup ∧ pending.ordered.length ≤ capacity ∧ pending.sealed = false

theorem empty_pending_invariant (capacity : Nat) :
    Invariant capacity TransferCurrentPendingReplay01.emptyPending := by
  exact ⟨fun _ => rfl, List.nodup_nil, Nat.zero_le capacity, rfl⟩

theorem append_preserves_coherence (previous : Pending) (keys : List Nat) (coherent : Coherent previous) :
    Coherent (appendPending previous keys) := by
  intro key
  change (previous.membership key || keys.contains key) = (previous.ordered ++ keys).contains key
  rw [coherent key, List.contains_append]

theorem unique_loop_derives_nodup_and_fresh (seen keys : List Nat) (accepted : uniqueLoop seen keys = true) :
    keys.Nodup ∧ ∀ key ∈ keys, key ∉ seen := by
  induction keys generalizing seen with
  | nil => exact ⟨List.nodup_nil, fun _ inside => by cases inside⟩
  | cons head rest ih =>
    cases held : seen.contains head with
    | true => simp only [uniqueLoop, held, if_true] at accepted; contradiction
    | false =>
      have remaining : uniqueLoop (head :: seen) rest = true := by
        simpa only [uniqueLoop, held, Bool.false_eq_true, if_false] using accepted
      obtain ⟨tailNodup, tailFresh⟩ := ih (head :: seen) remaining
      have headNotRest : head ∉ rest := fun inside => tailFresh head inside (by simp)
      have headNotSeen : head ∉ seen := by simpa using held
      refine ⟨List.nodup_cons.mpr ⟨headNotRest, tailNodup⟩, ?_⟩
      intro key inside inSeen
      cases List.mem_cons.mp inside with
      | inl same => subst key; exact headNotSeen inSeen
      | inr later => exact tailFresh key later (List.mem_cons_of_mem head inSeen)

theorem admitted_append_nodup (previous : Pending) (keys : List Nat)
    (coherent : Coherent previous) (oldNodup : previous.ordered.Nodup) (unique : uniqueLoop [] keys = true)
    (fresh : ∀ key ∈ keys, previous.membership key = false) :
    (appendPending previous keys).ordered.Nodup := by
  change (previous.ordered ++ keys).Nodup
  refine List.nodup_append.mpr ⟨oldNodup, (unique_loop_derives_nodup_and_fresh [] keys unique).1, ?_⟩
  intro old inOld key inKeys same
  subst key
  have absent := fresh old inKeys
  have present : previous.ordered.contains old = true := List.contains_iff_mem.mpr inOld
  rw [coherent old, present] at absent
  contradiction

theorem successful_inspection_preserves_invariant {O E : Type} (backend : Backend O E)
    (wordMax capacity : Nat) (child : Delta O E) (keys : List Nat) (next : Pending)
    (coherent : Coherent (backend.pending child)) (oldNodup : (backend.pending child).ordered.Nodup)
    (belowWord : capacity < wordMax) (success : inspect backend wordMax capacity child keys = .ok next) :
    Invariant capacity next := by
  have bounded := inspection_success_capacity_and_all_inputs backend wordMax capacity child keys next belowWord success
  obtain ⟨previous, _, previousEq, unique, _, _, _, _, _, nextEq⟩ :=
    inspection_success_order backend wordMax capacity child keys next success
  subst previous
  have nextCoherent : Coherent next := by
    rw [nextEq]
    exact append_preserves_coherence (backend.pending child) keys coherent
  have nextNodup : next.ordered.Nodup := by
    rw [nextEq]
    exact admitted_append_nodup (backend.pending child) keys coherent oldNodup unique
      (fun key inside => (bounded.2.2.2 key inside).2.1)
  exact ⟨nextCoherent, nextNodup, bounded.2.1, bounded.2.2.1⟩

set_option pp.all true in
#check @Coherent
#print axioms Coherent
set_option pp.all true in
#check @Invariant
#print axioms Invariant
set_option pp.all true in
#check @empty_pending_invariant
#print axioms empty_pending_invariant
set_option pp.all true in
#check @append_preserves_coherence
#print axioms append_preserves_coherence
set_option pp.all true in
#check @unique_loop_derives_nodup_and_fresh
#print axioms unique_loop_derives_nodup_and_fresh
set_option pp.all true in
#check @admitted_append_nodup
#print axioms admitted_append_nodup
set_option pp.all true in
#check @successful_inspection_preserves_invariant
#print axioms successful_inspection_preserves_invariant
end ShielddSecurity.TransferPendingSetInvariant01
