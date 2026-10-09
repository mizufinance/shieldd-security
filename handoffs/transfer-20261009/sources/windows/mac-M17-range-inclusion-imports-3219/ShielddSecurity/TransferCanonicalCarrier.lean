import Init.Data.List.Basic

set_option maxHeartbeats 100000

namespace ShielddSecurity.TransferCanonicalCarrier

/-!
Independent canonical decoder and exact registry/raw-byte cache model for the
complete native transaction carrier B. No hash inversion or effect-projection
injectivity is used. Actual protobuf/domain decoding, complete serialization,
artifact construction and Rust cache correspondence remain source obligations.
These lemmas do not verify proof capabilities, signatures or current state.
-/

def decodeCanonical {B : Type} (decode : List Nat → Option B)
    (encode : B → List Nat) (raw : List Nat) : Option B :=
  match decode raw with
  | none => none
  | some body => if encode body = raw then some body else none

theorem canonical_carrier_success {B : Type} (decode : List Nat → Option B)
    (encode : B → List Nat) (raw : List Nat) (body : B)
    (success : decodeCanonical decode encode raw = some body) :
    decode raw = some body ∧ encode body = raw := by
  cases result : decode raw with
  | none => simp [decodeCanonical, result] at success
  | some decoded =>
      by_cases canonical : encode decoded = raw
      · have same : decoded = body :=
          Option.some.inj (by simpa [decodeCanonical, result, canonical] using success)
        exact ⟨by simp only [same], by rw [← same]; exact canonical⟩
      · simp [decodeCanonical, result, canonical] at success

theorem same_raw_same_decoded {B : Type} (decode : List Nat → Option B)
    (encode : B → List Nat) (raw : List Nat) (first second : B)
    (a : decodeCanonical decode encode raw = some first)
    (b : decodeCanonical decode encode raw = some second) : first = second := by
  exact Option.some.inj (a.symm.trans b)

structure Cached (B : Type) where
  registry : Nat
  raw : List Nat
  body : B

def cacheLookup {B : Type} (registry : Nat) (raw : List Nat) (entry : Cached B) : Option B :=
  if entry.registry = registry ∧ entry.raw = raw then some entry.body else none

theorem cache_success_identity {B : Type} (registry : Nat) (raw : List Nat)
    (entry : Cached B) (body : B) (hit : cacheLookup registry raw entry = some body) :
    entry.registry = registry ∧ entry.raw = raw ∧ entry.body = body := by
  by_cases aligned : entry.registry = registry ∧ entry.raw = raw
  · exact ⟨aligned.1, aligned.2,
      Option.some.inj (by simpa [cacheLookup, aligned] using hit)⟩
  · simp [cacheLookup, aligned] at hit

/-- Cache-entry canonical association is a constructor invariant, separate
from proof verification and current-state admission. Native insert checks the
full retained transaction reencoding against raw bytes; its refinement is open. -/
theorem cache_canonical_carrier {B : Type} (decode : List Nat → Option B)
    (encode : B → List Nat) (registry : Nat) (raw : List Nat)
    (entry : Cached B) (body : B)
    (associated : decodeCanonical decode encode entry.raw = some entry.body)
    (hit : cacheLookup registry raw entry = some body) :
    decodeCanonical decode encode raw = some body ∧
    decode raw = some body ∧ encode body = raw := by
  have identity := cache_success_identity registry raw entry body hit
  have retained : decodeCanonical decode encode raw = some body := by
    rw [← identity.2.1, ← identity.2.2]
    exact associated
  exact ⟨retained, canonical_carrier_success decode encode raw body retained⟩

set_option pp.all true in
#check @canonical_carrier_success
#print axioms canonical_carrier_success
set_option pp.all true in
#check @same_raw_same_decoded
#print axioms same_raw_same_decoded
set_option pp.all true in
#check @cache_success_identity
#print axioms cache_success_identity
set_option pp.all true in
#check @cache_canonical_carrier
#print axioms cache_canonical_carrier

end ShielddSecurity.TransferCanonicalCarrier
