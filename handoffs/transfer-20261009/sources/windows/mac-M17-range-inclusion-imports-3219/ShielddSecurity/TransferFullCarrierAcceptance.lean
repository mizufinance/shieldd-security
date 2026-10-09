import Mathlib.Algebra.CharP.Defs
import ShielddSecurity.TransferCanonicalCarrier
import ShielddSecurity.TransferEnvelopeSourceBridge
import ShielddSecurity.TransferNativeSignaturePolicy
import ShielddSecurity.TransferLocalKeyShape
import ShielddSecurity.TransferSourceBridge
import ShielddSecurity.TransferIndexing
import ShielddSecurity.TransferSem
import ShielddSecurity.Rows

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferFullCarrierAcceptance

open TransferAcceptance TransferAdmission TransferProjection TransferSourceBridge TransferTransaction

/-!
Coherent modeled admission from a complete canonical carrier, without a supplied
BoundRows or desired Transfer poststate. Exact key, envelope, signature, current
pair/time and slot checks precede the independently defined effect program.
Verification modes remain distinct. Upstream proof knowledge supplies only an
exact satisfying compiled claim; the pending owned T1/T4 soundness interface
supplies TransferSem. Equal statement hashes yield matched full publicLc fields
or an explicit collision, never universal hash injectivity.

T is the complete transaction body and B the complete retained Transfer body.
The independent function record must still be instantiated against pinned Rust,
including all mixed-family and fee locations. Execution is the Transfer effect
portion: pay_fee/audit/other-family writes, native savepoints, NOMT/SCT persistence,
deferred flush, commit/recovery/publication and readback are separate OPEN joins.
-/

inductive VerificationMode where
  | individual | batch

def verifyIndependent (decode : List Nat → Option ClaimContext)
    (registry : TransferProofAdmissionModel.Registry) (verify : Item → Bool) :
    List Item → Option (List Capability)
  | [] => some []
  | item :: rest =>
      match TransferEnvelopeSourceBridge.verifyEncodedIndividual decode registry item (verify item) with
      | none => none
      | some capability =>
          match verifyIndependent decode registry verify rest with
          | none => none
          | some capabilities => some (capability :: capabilities)

def verifyForMode (mode : VerificationMode) (decode : List Nat → Option ClaimContext)
    (registry : TransferProofAdmissionModel.Registry) (individual : Item → Bool)
    (batch : List Item → Bool) (items : List Item) : Option (List Capability) :=
  match mode with
  | .individual => verifyIndependent decode registry individual items
  | .batch => match items with
      | [] => some []
      | first :: rest =>
          TransferEnvelopeSourceBridge.verifyEncodedBatch decode registry (first :: rest)
            (batch (first :: rest))

def attachRaw (registry : Nat) (expected : Nat → Item) :
    List Nat → List Capability → Option (List (Nat × Capability))
  | [], [] => some []
  | slot :: rest, capability :: remaining =>
      if capability.registry = registry ∧ capability.item = expected slot then
        match attachRaw registry expected rest remaining with
        | none => none
        | some rows => some ((slot, capability) :: rows)
      else none
  | _, _ => none

def attachRows (registry : Nat) (expected : Nat → Item)
    (slots : List Nat) (capabilities : List Capability) : Option (List (Nat × Capability)) :=
  if slots.Nodup then attachRaw registry expected slots capabilities else none

theorem attach_raw_success (registry : Nat) (expected : Nat → Item)
    (slots : List Nat) (capabilities : List Capability) (rows : List (Nat × Capability))
    (success : attachRaw registry expected slots capabilities = some rows) :
    rows.map Prod.fst = slots ∧
      ∀ row ∈ rows, row.2.registry = registry ∧ row.2.item = expected row.1 := by
  induction slots generalizing capabilities rows with
  | nil =>
      cases capabilities with
      | nil =>
          have same : [] = rows := Option.some.inj success
          subst rows
          exact ⟨rfl, by simp⟩
      | cons head rest =>
          simp only [attachRaw] at success
          cases success
  | cons slot rest ih =>
      cases capabilities with
      | nil =>
          simp only [attachRaw] at success
          cases success
      | cons capability remaining =>
          by_cases bound : capability.registry = registry ∧ capability.item = expected slot
          · cases attached : attachRaw registry expected rest remaining with
            | none =>
                simp only [attachRaw, if_pos bound, attached] at success
                cases success
            | some tailRows =>
                have same : (slot, capability) :: tailRows = rows := Option.some.inj
                  (by simpa only [attachRaw, if_pos bound, attached] using success)
                subst rows
                have tailFacts := ih remaining tailRows attached
                constructor
                · simpa only [List.map_cons, Prod.fst] using
                    congrArg (List.cons slot) tailFacts.1
                · intro row inside
                  rcases List.mem_cons.mp inside with same | present
                  · subst row
                    exact bound
                  · exact tailFacts.2 row present
          · simp only [attachRaw, if_neg bound] at success
            cases success

theorem attachment_derives_bound_rows (registry : Nat) (expected : Nat → Item)
    (slots : List Nat) (capabilities : List Capability) (rows : List (Nat × Capability))
    (success : attachRows registry expected slots capabilities = some rows) :
    BoundRows slots expected rows registry := by
  by_cases unique : slots.Nodup
  · have attached : attachRaw registry expected slots capabilities = some rows := by
      simpa only [attachRows, if_pos unique] using success
    have facts := attach_raw_success registry expected slots capabilities rows attached
    refine ⟨?_, ?_, facts.2⟩
    · rw [facts.1]
      exact unique
    · rw [facts.1]
  · simp only [attachRows, if_neg unique] at success
    cases success

structure Environment where
  noteRoots : List Nat
  currentPair : Pair
  history : Pair → Option TransferAdmission.Snapshot
  epoch : Nat
  historyNow : Nat
  grace : Nat
  blockTime : Int

def PairGate (environment : Environment) (requested : Pair) : Prop :=
  requested = environment.currentPair ∨
    match environment.history requested with
    | none => False
    | some snapshot => snapshot.pair = requested ∧ snapshot.epoch = environment.epoch ∧
        snapshot.observed ≤ environment.historyNow ∧ 0 < environment.grace ∧
        environment.historyNow - snapshot.observed ≤ environment.grace

instance (environment : Environment) (requested : Pair) : Decidable (PairGate environment requested) := by
  unfold PairGate
  cases environment.history requested <;> infer_instance

theorem pair_gate_admitted (environment : Environment) (requested : Pair)
    (accepted : PairGate environment requested) :
    PairAdmitted environment.currentPair requested (environment.history requested)
      environment.epoch environment.historyNow environment.grace := by
  rcases accepted with same | retained
  · exact Or.inl same
  · cases history : environment.history requested with
    | none =>
        simp only [history] at retained
    | some snapshot =>
        exact Or.inr ⟨snapshot, rfl, by simpa only [history] using retained⟩

def TimestampGate (environment : Environment) (target : Nat) : Prop :=
  0 ≤ environment.blockTime ∧ environment.blockTime < 2 ^ 63 ∧ target < 2 ^ 64 ∧ target ≠ 0 ∧
    (target - environment.blockTime.toNat) + (environment.blockTime.toNat - target) ≤ 1800

structure Model (T B : Type) where
  decode : List Nat → Option (TransferNativeSignaturePolicy.Carrier T)
  encode : TransferNativeSignaturePolicy.Carrier T → List Nat
  encodeBody : T → List Nat
  effectFields : T → List Nat
  authHash : List Nat → Nat
  effectHash : List Nat → Nat
  proofCount : T → Nat
  bindingKey : T → Nat
  spends : T → List TransferNativeSignaturePolicy.Spend
  slots : T → List Nat
  extract : T → Nat → SourceSlot B
  fields : B → List Nat
  effects : B → NativeBody
  pair : B → Pair
  timestamp : B → Nat

def expected {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto) (family : Nat)
    (carrier : TransferNativeSignaturePolicy.Carrier T) (index : Nat) : Item :=
  sourceItem family model.fields (crypto.hash .transferStatement) (model.extract carrier.body index)

def items {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto) (family : Nat)
    (carrier : TransferNativeSignaturePolicy.Carrier T) : List Item :=
  (model.slots carrier.body).map (expected model crypto family carrier)

def routed {T B : Type} (model : Model T B)
    (carrier : TransferNativeSignaturePolicy.Carrier T) : List RoutedSlot :=
  (model.slots carrier.body).map fun index => projectSlot model.effects (model.extract carrier.body index)

def CurrentBound {T B : Type} (model : Model T B) (environment : Environment)
    (carrier : TransferNativeSignaturePolicy.Carrier T) (entry : SourceSlot B) : Prop :=
  carrier.anchor ∈ environment.noteRoots ∧ PairGate environment (model.pair entry.body) ∧
    TimestampGate environment (model.timestamp entry.body)

instance {T B : Type} (model : Model T B) (environment : Environment)
    (carrier : TransferNativeSignaturePolicy.Carrier T) (entry : SourceSlot B) :
    Decidable (CurrentBound model environment carrier entry) := by
  unfold CurrentBound TimestampGate
  infer_instance

def checkCurrent {T B : Type} (model : Model T B) (environment : Environment)
    (carrier : TransferNativeSignaturePolicy.Carrier T) : List (SourceSlot B) → Option Unit
  | [] => some ()
  | first :: rest =>
      if CurrentBound model environment carrier first then checkCurrent model environment carrier rest else none

theorem current_checks_success {T B : Type} (model : Model T B) (environment : Environment)
    (carrier : TransferNativeSignaturePolicy.Carrier T) (entries : List (SourceSlot B))
    (success : checkCurrent model environment carrier entries = some ()) :
    ∀ entry ∈ entries, CurrentBound model environment carrier entry := by
  induction entries with
  | nil => simp
  | cons first rest ih =>
      by_cases bound : CurrentBound model environment carrier first
      · have tail : checkCurrent model environment carrier rest = some () := by
          simpa only [checkCurrent, if_pos bound] using success
        intro entry inside
        rcases List.mem_cons.mp inside with same | present
        · subst entry
          exact bound
        · exact ih tail entry present
      · simp only [checkCurrent, if_neg bound] at success
        cases success

theorem independent_checks_success (decode : List Nat → Option ClaimContext)
    (registry : TransferProofAdmissionModel.Registry) (verify : Item → Bool)
    (contract : Item → Prop)
    (checkedContract : ∀ item capability,
      TransferEnvelopeSourceBridge.verifyEncodedIndividual decode registry item (verify item) =
        some capability → contract item)
    (entries : List Item) (capabilities : List Capability)
    (success : verifyIndependent decode registry verify entries = some capabilities) :
    ∀ item ∈ entries, contract item := by
  induction entries generalizing capabilities with
  | nil => simp
  | cons first rest ih =>
      cases checked : TransferEnvelopeSourceBridge.verifyEncodedIndividual decode registry first (verify first) with
      | none => simp only [verifyIndependent, checked] at success; cases success
      | some capability =>
          cases remaining : verifyIndependent decode registry verify rest with
          | none => simp only [verifyIndependent, checked, remaining] at success; cases success
          | some tail =>
              intro item inside
              rcases List.mem_cons.mp inside with same | present
              · subst item
                exact checkedContract first capability checked
              · exact ih tail remaining item present

theorem mode_checks_success (mode : VerificationMode) (decode : List Nat → Option ClaimContext)
    (registry : TransferProofAdmissionModel.Registry) (individual : Item → Bool)
    (batch : List Item → Bool) (contract : Item → Prop)
    (individualContract : ∀ item capability,
      TransferEnvelopeSourceBridge.verifyEncodedIndividual decode registry item (individual item) =
        some capability → contract item)
    (batchContract : ∀ first rest capabilities,
      TransferEnvelopeSourceBridge.verifyEncodedBatch decode registry (first :: rest)
        (batch (first :: rest)) = some capabilities → ∀ item ∈ first :: rest, contract item)
    (entries : List Item) (capabilities : List Capability)
    (success : verifyForMode mode decode registry individual batch entries = some capabilities) :
    ∀ item ∈ entries, contract item := by
  cases mode with
  | individual =>
      exact independent_checks_success decode registry individual contract individualContract
        entries capabilities success
  | batch =>
      cases entries with
      | nil => simp
      | cons first rest => exact batchContract first rest capabilities success

structure Inputs where
  verificationMode : VerificationMode
  registry : TransferProofAdmissionModel.Registry
  family : Nat
  compiled : TransferLocalKeyShape.Relation
  key : TransferLocalKeyShape.Request
  decodeEnvelope : List Nat → Option ClaimContext
  individual : Item → Bool
  batch : List Item → Bool
  verifyBinding : Nat → Nat → List Nat → Bool
  verifySpend : Nat → Nat → List Nat → Bool

def Policy {T B : Type} (model : Model T B) (input : Inputs) (environment : Environment)
    (carrier : TransferNativeSignaturePolicy.Carrier T) : Prop :=
  TransferLocalKeyShape.RequestValid input.compiled input.key ∧
  input.registry.relation input.family = some input.key.key.relationDigest ∧
  TransferNativeSignaturePolicy.runPolicy model.encodeBody model.effectFields
    model.authHash model.effectHash model.proofCount model.bindingKey model.spends
    input.verifyBinding input.verifySpend carrier = some () ∧
  ((model.spends carrier.body).map TransferNativeSignaturePolicy.Spend.key).Nodup ∧
  checkCurrent model environment carrier
    ((model.slots carrier.body).map (model.extract carrier.body)) = some ()

instance {T B : Type} (model : Model T B) (input : Inputs) (environment : Environment)
    (carrier : TransferNativeSignaturePolicy.Carrier T) : Decidable (Policy model input environment carrier) := by
  unfold Policy
  infer_instance

structure Prepared (T : Type) where
  carrier : TransferNativeSignaturePolicy.Carrier T
  capabilities : List Capability
  rows : List (Nat × Capability)

def prepare {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (raw : List Nat) : Option (Prepared T) :=
  match TransferCanonicalCarrier.decodeCanonical model.decode model.encode raw with
  | none => none
  | some carrier =>
      if Policy model input environment carrier then
        match verifyForMode input.verificationMode input.decodeEnvelope input.registry
          input.individual input.batch (items model crypto input.family carrier) with
        | none => none
        | some capabilities =>
            match attachRows input.registry.identity (expected model crypto input.family carrier)
              (model.slots carrier.body) capabilities with
            | none => none
            | some rows => some ⟨carrier, capabilities, rows⟩
      else none

def PreparedFacts {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (raw : List Nat) (prepared : Prepared T) : Prop :=
  TransferCanonicalCarrier.decodeCanonical model.decode model.encode raw = some prepared.carrier ∧
  Policy model input environment prepared.carrier ∧
  verifyForMode input.verificationMode input.decodeEnvelope input.registry input.individual input.batch
    (items model crypto input.family prepared.carrier) = some prepared.capabilities ∧
  attachRows input.registry.identity (expected model crypto input.family prepared.carrier)
    (model.slots prepared.carrier.body) prepared.capabilities = some prepared.rows

theorem preparation_success {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (raw : List Nat) (prepared : Prepared T)
    (success : prepare model crypto input environment raw = some prepared) :
    PreparedFacts model crypto input environment raw prepared := by
  cases decoded : TransferCanonicalCarrier.decodeCanonical model.decode model.encode raw with
  | none => simp only [prepare, decoded] at success; cases success
  | some carrier =>
      by_cases policy : Policy model input environment carrier
      · cases verified : verifyForMode input.verificationMode input.decodeEnvelope input.registry
          input.individual input.batch (items model crypto input.family carrier) with
        | none => simp only [prepare, decoded, if_pos policy, verified] at success; cases success
        | some capabilities =>
            cases attached : attachRows input.registry.identity (expected model crypto input.family carrier)
                (model.slots carrier.body) capabilities with
            | none => simp only [prepare, decoded, if_pos policy, verified, attached] at success; cases success
            | some rows =>
                have same : (⟨carrier, capabilities, rows⟩ : Prepared T) = prepared :=
                  Option.some.inj (by simpa only [prepare, decoded, if_pos policy, verified, attached] using success)
                subst prepared
                exact ⟨decoded, policy, verified, attached⟩
      · simp only [prepare, decoded, if_neg policy] at success
        cases success

theorem preparation_canonical_and_bound {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (raw : List Nat) (prepared : Prepared T)
    (success : prepare model crypto input environment raw = some prepared) :
    (model.decode raw = some prepared.carrier ∧ model.encode prepared.carrier = raw) ∧
    BoundRows (model.slots prepared.carrier.body) (expected model crypto input.family prepared.carrier)
      prepared.rows input.registry.identity := by
  have facts := preparation_success model crypto input environment raw prepared success
  exact ⟨TransferCanonicalCarrier.canonical_carrier_success model.decode model.encode raw
    prepared.carrier facts.1, attachment_derives_bound_rows _ _ _ _ _ facts.2.2.2⟩

theorem preparation_current_slots {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (raw : List Nat) (prepared : Prepared T)
    (success : prepare model crypto input environment raw = some prepared) :
    ∀ index ∈ model.slots prepared.carrier.body,
      CurrentBound model environment prepared.carrier (model.extract prepared.carrier.body index) := by
  have facts := preparation_success model crypto input environment raw prepared success
  have checked := current_checks_success model environment prepared.carrier _ facts.2.1.2.2.2.2
  intro index inside
  exact checked _ (List.mem_map.mpr ⟨index, inside, rfl⟩)

theorem preparation_signature_arguments {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (raw : List Nat) (prepared : Prepared T)
    (success : prepare model crypto input environment raw = some prepared) :
    TransferNativeSignaturePolicy.bindingPolicy model.encodeBody model.authHash model.proofCount
      model.bindingKey input.verifyBinding prepared.carrier ∧
    ∀ spend ∈ model.spends prepared.carrier.body,
      TransferNativeSignaturePolicy.SpendBound input.verifySpend
        (model.effectHash (model.effectFields prepared.carrier.body)) prepared.carrier.anchor spend := by
  have facts := preparation_success model crypto input environment raw prepared success
  exact TransferNativeSignaturePolicy.full_carrier_signature_arguments _ _ _ _ _ _ _ _ _ _
    facts.2.1.2.2.1

/- The global proof interface supplies exact satisfying rows, opening and claim
coordinates, never a Transfer poststate. Its two modes are separate contracts.
The F/native scalar/commitment interpretation is part of the pending instantiation. -/
def CompiledClaim {F : Type} [Field F] (rows : List Row) (publicLc committed : Linear)
    (opens : List Nat → Nat → Prop) (item : Item) (claim : ClaimContext) : Prop :=
  ∃ (rho : Nat → F) (blinding : Nat), rho 0 = 1 ∧ Satisfies rho rows ∧
    eval rho publicLc = (item.statement : F) ∧ eval rho committed = (blinding : F) ∧
    item.statement < TransferCore.fieldModulus ∧ blinding < TransferCore.scalarOrder ∧
    opens claim.commitments blinding

structure UpstreamKnowledge {F : Type} [Field F] (input : Inputs)
    (rows : List Row) (publicLc committed : Linear) (opens : List Nat → Nat → Prop) : Prop where
  individual : ∀ item claim relation,
    input.decodeEnvelope item.envelope = some claim →
    input.registry.relation item.family = some relation → ClaimBound item.family relation item.statement claim →
    input.individual item = true → CompiledClaim (F := F) rows publicLc committed opens item claim
  batch : ∀ (first : TransferProofAdmissionModel.Entry) rest relation,
    input.registry.relation first.item.family = some relation →
    (∀ entry ∈ first :: rest, input.decodeEnvelope entry.item.envelope = some entry.claim) →
    (∀ entry ∈ first :: rest, TransferProofAdmissionModel.ContextBound first.item.family relation entry) →
    input.batch ((first :: rest).map TransferProofAdmissionModel.Entry.item) = true →
    ∀ entry ∈ first :: rest, CompiledClaim (F := F) rows publicLc committed opens entry.item entry.claim

theorem verified_compiled_claims {F : Type} [Field F] (input : Inputs)
    (rows : List Row) (publicLc committed : Linear) (opens : List Nat → Nat → Prop)
    (knowledge : UpstreamKnowledge (F := F) input rows publicLc committed opens)
    (entries : List Item) (capabilities : List Capability)
    (success : verifyForMode input.verificationMode input.decodeEnvelope input.registry
      input.individual input.batch entries = some capabilities) :
    ∀ item ∈ entries, ∃ claim, input.decodeEnvelope item.envelope = some claim ∧
      CompiledClaim (F := F) rows publicLc committed opens item claim := by
  apply mode_checks_success input.verificationMode input.decodeEnvelope input.registry input.individual
    input.batch (fun item => ∃ claim, input.decodeEnvelope item.envelope = some claim ∧
      CompiledClaim (F := F) rows publicLc committed opens item claim) ?_ ?_ entries capabilities success
  · intro item capability checked
    obtain ⟨claim, relation, decoded, lookup, bound, verified, _⟩ :=
      TransferEnvelopeSourceBridge.individual_envelope_join _ _ _ _ _ checked
    exact ⟨claim, decoded, knowledge.individual item claim relation decoded lookup bound verified⟩
  · intro first rest caps checked item inside
    obtain ⟨entry, tail, relation, _, source, decoded, lookup, contexts, verified, _, _⟩ :=
      TransferEnvelopeSourceBridge.batch_envelope_join _ _ _ _ _ checked
    have member : item ∈ (entry :: tail).map TransferProofAdmissionModel.Entry.item := source.symm ▸ inside
    obtain ⟨native, present, same⟩ := List.mem_map.mp member
    subst item
    exact ⟨native.claim, decoded native present,
      knowledge.batch entry tail relation lookup decoded contexts (source.symm ▸ verified) native present⟩

/- Pending local T1/T4 interface for the exact compiled relation. This is
explicitly a premise to instantiate, not a proved whole-circuit theorem. -/
def LocalRowSoundness {F : Type} [Field F] [CharP F TransferCore.fieldModulus] (crypto : TransferSem.Crypto)
    (rows : List Row) (publicLc committed : Linear) (opens : List Nat → Nat → Prop) : Prop :=
  ∀ (item : Item) (claim : ClaimContext) (rho : Nat → F) (blinding : Nat),
    rho 0 = 1 → Satisfies rho rows → eval rho publicLc = (item.statement : F) →
    eval rho committed = (blinding : F) → item.statement < TransferCore.fieldModulus →
    blinding < TransferCore.scalarOrder → opens claim.commitments blinding →
    ∃ witness, TransferSem.TransferSem crypto witness ∧ witness.blinding = blinding ∧
      item.statement = crypto.hash .transferStatement (TransferSem.publicFields crypto witness)

def SemanticOrCollision {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (entry : SourceSlot B) : Prop :=
  ∃ witness, TransferSem.TransferSem crypto witness ∧
    (model.fields entry.body = TransferSem.publicFields crypto witness ∨
      (model.fields entry.body ≠ TransferSem.publicFields crypto witness ∧
        crypto.hash .transferStatement (model.fields entry.body) =
          crypto.hash .transferStatement (TransferSem.publicFields crypto witness)))

theorem preparation_semantic_or_collision {T B F : Type} [Field F] [CharP F TransferCore.fieldModulus]
    (model : Model T B) (crypto : TransferSem.Crypto) (input : Inputs) (environment : Environment)
    (rows : List Row) (publicLc committed : Linear) (opens : List Nat → Nat → Prop)
    (knowledge : UpstreamKnowledge (F := F) input rows publicLc committed opens)
    (soundness : LocalRowSoundness (F := F) crypto rows publicLc committed opens)
    (raw : List Nat) (prepared : Prepared T)
    (success : prepare model crypto input environment raw = some prepared) :
    ∀ index ∈ model.slots prepared.carrier.body,
      SemanticOrCollision model crypto (model.extract prepared.carrier.body index) := by
  have facts := preparation_success model crypto input environment raw prepared success
  have claims := verified_compiled_claims input rows publicLc committed opens knowledge _ _ facts.2.2.1
  intro index inside
  obtain ⟨claim, _, realized⟩ := claims (expected model crypto input.family prepared.carrier index)
    (List.mem_map.mpr ⟨index, inside, rfl⟩)
  obtain ⟨rho, blinding, one, satisfied, publicEq, committedEq, canonical, bound, opening⟩ := realized
  obtain ⟨witness, semantic, _, statement⟩ :=
    soundness _ claim rho blinding one satisfied publicEq committedEq canonical bound opening
  refine ⟨witness, semantic, ?_⟩
  by_cases same : model.fields (model.extract prepared.carrier.body index).body =
      TransferSem.publicFields crypto witness
  · exact Or.inl same
  · exact Or.inr ⟨same, statement⟩

def run {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto) (input : Inputs)
    (environment : Environment) (mode : TransferIndexing.Mode) (state : TransferIndexing.State)
    (transaction : Nat) (raw : List Nat) : Option (Prepared T × TransferIndexing.State) :=
  match prepare model crypto input environment raw with
  | none => none
  | some prepared =>
      (TransferIndexing.runTransaction mode state (routed model prepared.carrier) transaction).map
        fun after => (prepared, after)

theorem full_carrier_pending_effects {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (mode : TransferIndexing.Mode)
    (state after : TransferIndexing.State) (transaction : Nat) (raw : List Nat) (prepared : Prepared T)
    (success : run model crypto input environment mode state transaction raw = some (prepared, after)) :
    prepare model crypto input environment raw = some prepared ∧
    PreparedFacts model crypto input environment raw prepared ∧
    after = TransferIndexing.recordIndex mode
      { state with effects := applyRoutedSlots state.effects (routed model prepared.carrier) } transaction := by
  cases checked : prepare model crypto input environment raw with
  | none => simp only [run, checked] at success; cases success
  | some retained =>
      cases effects : TransferIndexing.runTransaction mode state (routed model retained.carrier) transaction with
      | none => simp only [run, checked, effects, Option.map_none] at success; cases success
      | some result =>
          have same : (retained, result) = (prepared, after) :=
            Option.some.inj (by simpa only [run, checked, effects, Option.map_some] using success)
          have carrierSame : retained = prepared := congrArg Prod.fst same
          have stateSame : result = after := congrArg Prod.snd same
          subst retained
          subst result
          exact ⟨rfl, preparation_success _ _ _ _ _ _ checked,
            TransferIndexing.mode_transaction_success mode state after _ transaction effects⟩

structure Consequence {T B : Type} (model : Model T B) (crypto : TransferSem.Crypto)
    (input : Inputs) (environment : Environment) (mode : TransferIndexing.Mode)
    (state after : TransferIndexing.State) (transaction : Nat) (raw : List Nat)
    (prepared : Prepared T) : Prop where
  canonical : model.decode raw = some prepared.carrier ∧ model.encode prepared.carrier = raw
  keyShape : TransferLocalKeyShape.RequestValid input.compiled input.key
  familyKey : input.registry.relation input.family = some input.key.key.relationDigest
  rowsBound : BoundRows (model.slots prepared.carrier.body)
    (expected model crypto input.family prepared.carrier) prepared.rows input.registry.identity
  binding : TransferNativeSignaturePolicy.bindingPolicy model.encodeBody model.authHash model.proofCount
    model.bindingKey input.verifyBinding prepared.carrier
  spends : ∀ spend ∈ model.spends prepared.carrier.body,
    TransferNativeSignaturePolicy.SpendBound input.verifySpend
      (model.effectHash (model.effectFields prepared.carrier.body)) prepared.carrier.anchor spend
  uniqueSpendKeys : ((model.spends prepared.carrier.body).map TransferNativeSignaturePolicy.Spend.key).Nodup
  current : ∀ index ∈ model.slots prepared.carrier.body,
    CurrentBound model environment prepared.carrier (model.extract prepared.carrier.body index)
  semantic : ∀ index ∈ model.slots prepared.carrier.body,
    SemanticOrCollision model crypto (model.extract prepared.carrier.body index)
  pendingEffects : after = TransferIndexing.recordIndex mode
    { state with effects := applyRoutedSlots state.effects (routed model prepared.carrier) } transaction

theorem full_carrier_acceptance_consequence {T B F : Type} [Field F] [CharP F TransferCore.fieldModulus]
    (model : Model T B) (crypto : TransferSem.Crypto) (input : Inputs) (environment : Environment)
    (rows : List Row) (publicLc committed : Linear) (opens : List Nat → Nat → Prop)
    (knowledge : UpstreamKnowledge (F := F) input rows publicLc committed opens)
    (soundness : LocalRowSoundness (F := F) crypto rows publicLc committed opens)
    (mode : TransferIndexing.Mode) (state after : TransferIndexing.State)
    (transaction : Nat) (raw : List Nat) (prepared : Prepared T)
    (success : run model crypto input environment mode state transaction raw = some (prepared, after)) :
    Consequence model crypto input environment mode state after transaction raw prepared := by
  obtain ⟨checked, facts, effectResult⟩ := full_carrier_pending_effects model crypto input environment
    mode state after transaction raw prepared success
  have canonicalBound := preparation_canonical_and_bound model crypto input environment raw prepared checked
  have signatureArguments := preparation_signature_arguments model crypto input environment raw prepared checked
  exact ⟨canonicalBound.1, facts.2.1.1, facts.2.1.2.1, canonicalBound.2,
    signatureArguments.1, signatureArguments.2, facts.2.1.2.2.2.1,
    preparation_current_slots model crypto input environment raw prepared checked,
    preparation_semantic_or_collision model crypto input environment rows publicLc committed opens
      knowledge soundness raw prepared checked, effectResult⟩

set_option pp.all true in
#check @attach_raw_success
#print axioms attach_raw_success
set_option pp.all true in
#check @attachment_derives_bound_rows
#print axioms attachment_derives_bound_rows
set_option pp.all true in
#check @pair_gate_admitted
#print axioms pair_gate_admitted
set_option pp.all true in
#check @current_checks_success
#print axioms current_checks_success
set_option pp.all true in
#check @independent_checks_success
#print axioms independent_checks_success
set_option pp.all true in
#check @mode_checks_success
#print axioms mode_checks_success
set_option pp.all true in
#check @preparation_success
#print axioms preparation_success
set_option pp.all true in
#check @preparation_canonical_and_bound
#print axioms preparation_canonical_and_bound
set_option pp.all true in
#check @preparation_current_slots
#print axioms preparation_current_slots
set_option pp.all true in
#check @preparation_signature_arguments
#print axioms preparation_signature_arguments
set_option pp.all true in
#check @verified_compiled_claims
#print axioms verified_compiled_claims
set_option pp.all true in
#check @preparation_semantic_or_collision
#print axioms preparation_semantic_or_collision
set_option pp.all true in
#check @full_carrier_pending_effects
#print axioms full_carrier_pending_effects
set_option pp.all true in
#check @full_carrier_acceptance_consequence
#print axioms full_carrier_acceptance_consequence

end ShielddSecurity.TransferFullCarrierAcceptance
