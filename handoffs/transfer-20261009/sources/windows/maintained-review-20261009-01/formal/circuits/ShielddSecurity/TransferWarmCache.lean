import ShielddSecurity.TransferFullCarrierAcceptance

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferWarmCache

open TransferAcceptance TransferProjection TransferSourceBridge TransferTransaction
open TransferFullCarrierAcceptance

/-!
The cache constructor retains only a result of the modeled complete canonical
stateless construction. No historical/current state is stored as authorization.
Each hit binds exact registry/raw bytes and reruns current checks followed by
the independently defined effect program. Native stateless insertion happens
even if historical checking later fails; the constructor therefore performs no
current-state check. Memory eviction/hash indexing/proposal historical-context
sharing, actual Rust artifact constructors and authenticated state remain OPEN.
-/

structure Cached (T : Type) where
  registry : Nat
  raw : List Nat
  prepared : Prepared T

def StatelessPolicy {T B : Type} (model : Model T B) (input : Inputs)
    (carrier : TransferNativeSignaturePolicy.Carrier T) : Prop :=
  TransferLocalKeyShape.RequestValid input.compiled input.key ∧
  input.registry.relation input.family = some input.key.key.relationDigest ∧
  TransferNativeSignaturePolicy.runPolicy model.encodeBody model.effectFields
    model.authHash model.effectHash model.proofCount model.bindingKey model.spends
    input.verifyBinding input.verifySpend carrier = some () ∧
  ((model.spends carrier.body).map TransferNativeSignaturePolicy.Spend.key).Nodup

instance {T B : Type} (model : Model T B) (input : Inputs)
    (carrier : TransferNativeSignaturePolicy.Carrier T) : Decidable (StatelessPolicy model input carrier) := by
  unfold StatelessPolicy
  infer_instance

def construct {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (raw : List Nat) : Option (Cached T) :=
  match TransferCanonicalCarrier.decodeCanonical model.decode model.encode raw with
  | none => none
  | some carrier =>
      if StatelessPolicy model input carrier then
        match verifyForMode input.verificationMode input.decodeEnvelope input.registry
          input.individual input.batch (items model crypto input.family carrier) with
        | none => none
        | some capabilities =>
            match attachRows input.registry.identity (expected model crypto input.family carrier)
              (model.slots carrier.body) capabilities with
            | none => none
            | some rows => some ⟨input.registry.identity, raw, ⟨carrier, capabilities, rows⟩⟩
      else none

theorem constructor_success {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (raw : List Nat) (entry : Cached T)
    (success : construct model crypto input raw = some entry) :
    entry.registry = input.registry.identity ∧ entry.raw = raw ∧
    (model.decode raw = some entry.prepared.carrier ∧ model.encode entry.prepared.carrier = raw) ∧
    StatelessPolicy model input entry.prepared.carrier ∧
    verifyForMode input.verificationMode input.decodeEnvelope input.registry input.individual input.batch
      (items model crypto input.family entry.prepared.carrier) = some entry.prepared.capabilities ∧
    attachRows input.registry.identity (expected model crypto input.family entry.prepared.carrier)
      (model.slots entry.prepared.carrier.body) entry.prepared.capabilities = some entry.prepared.rows := by
  cases decoded : TransferCanonicalCarrier.decodeCanonical model.decode model.encode raw with
  | none => simp only [construct, decoded] at success; cases success
  | some carrier =>
      by_cases policy : StatelessPolicy model input carrier
      · cases verified : verifyForMode input.verificationMode input.decodeEnvelope input.registry
          input.individual input.batch (items model crypto input.family carrier) with
        | none => simp only [construct, decoded, if_pos policy, verified] at success; cases success
        | some capabilities =>
            cases attached : attachRows input.registry.identity (expected model crypto input.family carrier)
                (model.slots carrier.body) capabilities with
            | none => simp only [construct, decoded, if_pos policy, verified, attached] at success; cases success
            | some rows =>
                have same : (⟨input.registry.identity, raw, ⟨carrier, capabilities, rows⟩⟩ : Cached T) = entry :=
                  Option.some.inj (by simpa only [construct, decoded, if_pos policy, verified, attached] using success)
                subst entry
                exact ⟨rfl, rfl, TransferCanonicalCarrier.canonical_carrier_success _ _ _ _ decoded,
                  policy, verified, attached⟩
      · simp only [construct, decoded, if_neg policy] at success
        cases success

def HitGate {T B : Type} (model : Model T B) (environment : Environment)
    (registry : Nat) (raw : List Nat) (entry : Cached T) : Prop :=
  entry.registry = registry ∧ entry.raw = raw ∧
    checkCurrent model environment entry.prepared.carrier
      ((model.slots entry.prepared.carrier.body).map (model.extract entry.prepared.carrier.body)) = some ()

instance {T B : Type} (model : Model T B) (environment : Environment)
    (registry : Nat) (raw : List Nat) (entry : Cached T) :
    Decidable (HitGate model environment registry raw entry) := by
  unfold HitGate
  infer_instance

def deliver {T B : Type} (model : Model T B) (environment : Environment)
    (registry : Nat) (raw : List Nat) (entry : Cached T) (mode : TransferIndexing.Mode)
    (state : TransferIndexing.State) (transaction : Nat) : Option TransferIndexing.State :=
  if HitGate model environment registry raw entry then
    TransferIndexing.runTransaction mode state (routed model entry.prepared.carrier) transaction
  else none

theorem warm_success_checks_current {T B : Type} (model : Model T B) (environment : Environment)
    (registry : Nat) (raw : List Nat) (entry : Cached T) (mode : TransferIndexing.Mode)
    (state after : TransferIndexing.State) (transaction : Nat)
    (success : deliver model environment registry raw entry mode state transaction = some after) :
    entry.registry = registry ∧ entry.raw = raw ∧
    (∀ index ∈ model.slots entry.prepared.carrier.body,
      CurrentBound model environment entry.prepared.carrier (model.extract entry.prepared.carrier.body index)) ∧
    after = TransferIndexing.recordIndex mode
      { state with effects := applyRoutedSlots state.effects (routed model entry.prepared.carrier) } transaction := by
  by_cases hit : HitGate model environment registry raw entry
  · have execution : TransferIndexing.runTransaction mode state (routed model entry.prepared.carrier)
        transaction = some after := by simpa only [deliver, if_pos hit] using success
    refine ⟨hit.1, hit.2.1, ?_, TransferIndexing.mode_transaction_success _ _ _ _ _ execution⟩
    have current := current_checks_success model environment entry.prepared.carrier _ hit.2.2
    intro index inside
    exact current _ (List.mem_map.mpr ⟨index, inside, rfl⟩)
  · simp only [deliver, if_neg hit] at success
    cases success

theorem constructed_warm_carrier_and_rows {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (constructedRaw raw : List Nat)
    (entry : Cached T) (mode : TransferIndexing.Mode) (state after : TransferIndexing.State)
    (transaction : Nat)
    (constructed : construct model crypto input constructedRaw = some entry)
    (success : deliver model environment input.registry.identity raw entry mode state transaction = some after) :
    model.decode raw = some entry.prepared.carrier ∧ model.encode entry.prepared.carrier = raw ∧
    BoundRows (model.slots entry.prepared.carrier.body)
      (expected model crypto input.family entry.prepared.carrier) entry.prepared.rows input.registry.identity := by
  have made := constructor_success model crypto input constructedRaw entry constructed
  have warm := warm_success_checks_current model environment input.registry.identity raw entry mode state after transaction success
  have same : constructedRaw = raw := made.2.1.symm.trans warm.2.1
  exact ⟨by simpa only [same] using made.2.2.1.1,
    by simpa only [same] using made.2.2.1.2,
    attachment_derives_bound_rows _ _ _ _ _ made.2.2.2.2.2⟩

theorem stale_current_cache_refused {T B : Type} (model : Model T B) (environment : Environment)
    (registry : Nat) (raw : List Nat) (entry : Cached T) (mode : TransferIndexing.Mode)
    (state : TransferIndexing.State) (transaction : Nat)
    (stale : checkCurrent model environment entry.prepared.carrier
      ((model.slots entry.prepared.carrier.body).map (model.extract entry.prepared.carrier.body)) = none) :
    deliver model environment registry raw entry mode state transaction = none := by
  have missing : ¬ HitGate model environment registry raw entry := by
    intro hit
    have impossible : (none : Option Unit) = some () := stale.symm.trans hit.2.2
    cases impossible
  simp only [deliver, if_neg missing]

theorem wrong_registry_cache_refused {T B : Type} (model : Model T B) (environment : Environment)
    (registry : Nat) (raw : List Nat) (entry : Cached T) (mode : TransferIndexing.Mode)
    (state : TransferIndexing.State) (transaction : Nat) (wrong : entry.registry ≠ registry) :
    deliver model environment registry raw entry mode state transaction = none := by
  have missing : ¬ HitGate model environment registry raw entry := fun hit => wrong hit.1
  simp only [deliver, if_neg missing]

theorem wrong_bytes_cache_refused {T B : Type} (model : Model T B) (environment : Environment)
    (registry : Nat) (raw : List Nat) (entry : Cached T) (mode : TransferIndexing.Mode)
    (state : TransferIndexing.State) (transaction : Nat) (wrong : entry.raw ≠ raw) :
    deliver model environment registry raw entry mode state transaction = none := by
  have missing : ¬ HitGate model environment registry raw entry := fun hit => wrong hit.2.1
  simp only [deliver, if_neg missing]

set_option pp.all true in
#check @constructor_success
#print axioms constructor_success
set_option pp.all true in
#check @warm_success_checks_current
#print axioms warm_success_checks_current
set_option pp.all true in
#check @constructed_warm_carrier_and_rows
#print axioms constructed_warm_carrier_and_rows
set_option pp.all true in
#check @stale_current_cache_refused
#print axioms stale_current_cache_refused
set_option pp.all true in
#check @wrong_registry_cache_refused
#print axioms wrong_registry_cache_refused
set_option pp.all true in
#check @wrong_bytes_cache_refused
#print axioms wrong_bytes_cache_refused

end ShielddSecurity.TransferWarmCache
