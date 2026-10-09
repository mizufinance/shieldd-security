import ShielddSecurity.TransferNativeSignatureWrapper

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferRandomizedSigningLog

variable {F : Type} [Field F]
  {E S R K Q Signing J Message Signature : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-! Deterministic bookkeeping for an adaptive, multi-user, randomized-key
signature experiment. These definitions do not supply a security bound, a
secret key, or an honest registration for an adversarially chosen key. Honest
key generation, native signing-oracle simulation and the distribution of the
whole experiment must be supplied by the separate standard RedDSA game.
Corruption is tracked by canonical base-key bytes, across party identifiers.
Every permitted signing attempt logs the actual derived key and exact message,
including attempts whose primitive signer returns no signature. -/

inductive Origin where
  | honest
  | adversarial
  deriving DecidableEq

structure Registration (K : Type) where
  party : Nat
  base : K
  origin : Origin

structure Request (K Message : Type) where
  key : K
  message : Message

structure State (K Message : Type) where
  registrations : List (Registration K)
  corrupted : List GroupByteCodec.Bytes
  requests : List (Request K Message)

def register (state : State K Message) (entry : Registration K) : State K Message :=
  { state with registrations := entry :: state.registrations }

def corrupt (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (state : State K Message) (base : K) : State K Message :=
  { state with corrupted := upstream.keyBytes base :: state.corrupted }

def Protected (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (state : State K Message) (entry : Registration K) : Prop :=
  entry ∈ state.registrations ∧ entry.origin = .honest ∧
    upstream.keyBytes entry.base ∉ state.corrupted

def recordAttempt
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (state : State K Message) (base : K) (randomizer : R) (message : Message) :
    State K Message :=
  { state with requests := ⟨upstream.randomize base randomizer,message⟩ :: state.requests }

/-- Permission to query the experiment is separate from this transition.
The transition always records an already permitted request, before observing
the primitive signer's result. Native signing-key derivation remains in the
oracle simulation; it is not inferred from a verification result. -/
def signAttempt
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (sign : K → R → Message → Option Signature)
    (state : State K Message) (base : K) (randomizer : R) (message : Message) :
    State K Message × Option Signature :=
  (recordAttempt upstream state base randomizer message, sign base randomizer message)

theorem register_fields (state : State K Message) (entry : Registration K) :
    entry ∈ (register state entry).registrations ∧
      (register state entry).corrupted = state.corrupted ∧
      (register state entry).requests = state.requests :=
  ⟨List.mem_cons_self,rfl,rfl⟩

theorem corruption_recorded
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (state : State K Message) (base : K) :
    upstream.keyBytes base ∈ (corrupt upstream state base).corrupted ∧
      (corrupt upstream state base).registrations = state.registrations ∧
      (corrupt upstream state base).requests = state.requests :=
  ⟨List.mem_cons_self,rfl,rfl⟩

theorem signing_records_attempt
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (sign : K → R → Message → Option Signature)
    (state : State K Message) (base : K) (randomizer : R) (message : Message) :
    (⟨upstream.randomize base randomizer,message⟩ : Request K Message) ∈
      (signAttempt upstream sign state base randomizer message).1.requests :=
  List.mem_cons_self

theorem signing_arguments
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (sign : K → R → Message → Option Signature)
    (state : State K Message) (base : K) (randomizer : R) (message : Message) :
    (signAttempt upstream sign state base randomizer message).2 = sign base randomizer message ∧
      (signAttempt upstream sign state base randomizer message).1.registrations = state.registrations ∧
      (signAttempt upstream sign state base randomizer message).1.corrupted = state.corrupted :=
  ⟨rfl,rfl,rfl⟩

theorem failed_signing_recorded
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (sign : K → R → Message → Option Signature)
    (state : State K Message) (base : K) (randomizer : R) (message : Message)
    (failed : sign base randomizer message = none) :
    (signAttempt upstream sign state base randomizer message).2 = none ∧
      (⟨upstream.randomize base randomizer,message⟩ : Request K Message) ∈
        (signAttempt upstream sign state base randomizer message).1.requests :=
  ⟨failed,signing_records_attempt upstream sign state base randomizer message⟩

theorem old_query_preserved
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (state : State K Message) (base : K) (randomizer : R) (message : Message)
    (old : Request K Message) (recorded : old ∈ state.requests) :
    old ∈ (recordAttempt upstream state base randomizer message).requests :=
  List.mem_cons_of_mem _ recorded

theorem duplicate_registration_corruption
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (state : State K Message) (base : K) (entry : Registration K)
    (sameBytes : upstream.keyBytes entry.base = upstream.keyBytes base) :
    ¬ Protected upstream (corrupt upstream state base) entry := by
  intro protectedEntry
  apply protectedEntry.2.2
  rw [sameBytes]
  exact List.mem_cons_self

/-- A caller may compress its native log only by mapping every recorded query.
Absence from that complete mapped log implies native absence without assuming
injectivity of a key label, effect hash, or message projection. The reverse
implication is deliberately not asserted. -/
theorem unqueried_native_from_mapped {Label : Type}
    (project : Request K Message → Label) (requests : List (Request K Message))
    (target : Request K Message) (absent : project target ∉ requests.map project) :
    target ∉ requests := by
  intro inside
  exact absent (List.mem_map.mpr ⟨target,inside,rfl⟩)

theorem protected_base
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (state : State K Message) (entry : Registration K)
    (protectedEntry : Protected upstream state entry) :
    entry ∈ state.registrations ∧ entry.origin = .honest ∧
      upstream.keyBytes entry.base ∉ state.corrupted := protectedEntry

/-- Exact winning-event predicate, not a theorem that an accepted Transfer is
unqueried or honestly registered. Randomizers are adversarial choices; queries
from every party and action must already be in the shared signing log. -/
def Forgery
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verify : K → Message → Signature → Bool) (state : State K Message)
    (entry : Registration K) (randomizer : R) (message : Message)
    (signature : Signature) : Prop :=
  Protected upstream state entry ∧
    verify (upstream.randomize entry.base randomizer) message signature = true ∧
    (⟨upstream.randomize entry.base randomizer,message⟩ : Request K Message) ∉ state.requests

theorem wrapper_game_event
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verify : K → Message → Signature → Bool) (state : State K Message)
    (entry : Registration K) (randomizer : R) (message : Message) (signature : Signature)
    (protectedEntry : Protected upstream state entry)
    (unqueried : (⟨upstream.randomize entry.base randomizer,message⟩ : Request K Message) ∉ state.requests)
    (accepted : TransferNativeSignatureWrapper.verifyAuth upstream verify
      (ShielddNativeSdk.planRk upstream entry.base randomizer) message signature = some ()) :
    Forgery upstream verify state entry randomizer message signature ∧
      upstream.embed (upstream.keyPoint (upstream.randomize entry.base randomizer)) =
        upstream.embed (upstream.keyPoint entry.base) +
          fr.integer randomizer • upstream.embed (upstream.promote upstream.spendAuthSubgroup) ∧
      upstream.embed (upstream.keyPoint (upstream.randomize entry.base randomizer)) ≠ 0 := by
  have checked := TransferNativeSignatureWrapper.randomized_key_argument upstream verify
    entry.base randomizer message signature accepted
  exact ⟨⟨protectedEntry,checked.2.2,unqueried⟩,checked.1,checked.2.1⟩

set_option pp.all true in
#check @register_fields
#print axioms register_fields
set_option pp.all true in
#check @corruption_recorded
#print axioms corruption_recorded
set_option pp.all true in
#check @signing_records_attempt
#print axioms signing_records_attempt
set_option pp.all true in
#check @signing_arguments
#print axioms signing_arguments
set_option pp.all true in
#check @failed_signing_recorded
#print axioms failed_signing_recorded
set_option pp.all true in
#check @old_query_preserved
#print axioms old_query_preserved
set_option pp.all true in
#check @duplicate_registration_corruption
#print axioms duplicate_registration_corruption
set_option pp.all true in
#check @unqueried_native_from_mapped
#print axioms unqueried_native_from_mapped
set_option pp.all true in
#check @protected_base
#print axioms protected_base
set_option pp.all true in
#check @wrapper_game_event
#print axioms wrapper_game_event

end ShielddSecurity.TransferRandomizedSigningLog
