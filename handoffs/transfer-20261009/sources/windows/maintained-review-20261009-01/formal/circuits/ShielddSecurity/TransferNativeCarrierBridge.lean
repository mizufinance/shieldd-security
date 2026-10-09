import ShielddSecurity.TransferStatement
import ShielddSecurity.RuntimeTransferStatement
import ShielddSecurity.TransferFullCarrierAcceptance

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferNativeCarrierBridge

open TransferAcceptance TransferProjection TransferSourceBridge TransferFullCarrierAcceptance

/-!
Exact decoded native public-view construction: Family::Transfer is 1. The full
64-field statement and independently retained whole payloads come from one
action view. Source::transfer_extract_public supplies the transaction context
anchor; public_input_hash supplies the proof-context field. Neither comes from
hash inversion. The native codecs, payload/recovery commitments, group/field
coordinates and conversion of the complete Rust action into this view remain
explicit local contracts. This is not a full Rust refinement or crypto proof.
-/

inductive Context where
  | ordinary | feeFunding

def Context.code : Context → Nat
  | .ordinary => 1
  | .feeFunding => 2

def Context.isOrdinary : Context → Bool
  | .ordinary => true
  | .feeFunding => false

structure ActionView where
  decodedFields : TransferStatement Nat
  contextAnchor : Nat
  bodyAnchor : Nat
  context : Context
  recipientPayload : Nat
  changePayload : Nat
  volumePayload : Nat

structure NativeTransaction (B : Type) where
  body : B
  anchor : Nat
  bindingSignature : List Nat

def carrier {B : Type} (transaction : NativeTransaction B) :
    TransferNativeSignaturePolicy.Carrier (NativeTransaction B) :=
  ⟨transaction, transaction.anchor, transaction.bindingSignature⟩

def decodeCarrier {B : Type} (decode : List Nat → Option (NativeTransaction B)) (raw : List Nat) :
    Option (TransferNativeSignaturePolicy.Carrier (NativeTransaction B)) :=
  (decode raw).map carrier

theorem native_decoder_context {B : Type} (decode : List Nat → Option (NativeTransaction B))
    (raw : List Nat) (decoded : TransferNativeSignaturePolicy.Carrier (NativeTransaction B))
    (success : decodeCarrier decode raw = some decoded) :
    decoded.anchor = decoded.body.anchor ∧ decoded.bindingSignature = decoded.body.bindingSignature := by
  cases native : decode raw with
  | none => simp only [decodeCarrier, native, Option.map_none] at success; cases success
  | some transaction =>
      have same : carrier transaction = decoded :=
        Option.some.inj (by simpa only [decodeCarrier, native, Option.map_some] using success)
      rw [← same]
      exact ⟨rfl, rfl⟩

def statement (action : ActionView) : TransferStatement Nat :=
  { action.decodedFields with anchor := action.contextAnchor, volumeContext := action.context.code }

def project (action : ActionView) : NativeBody :=
  { spend0 := action.decodedFields.firstNullifier
    spend1 := action.decodedFields.secondNullifier
    output0 := ⟨action.decodedFields.recipientNote, action.recipientPayload⟩
    output1 := ⟨action.decodedFields.changeNote, action.changePayload⟩
    volume := ⟨action.decodedFields.volumeDayStart, action.decodedFields.volumeNullifier,
      action.decodedFields.volumeCommitment, action.volumePayload⟩
    ordinaryContext := action.context.isOrdinary }

def transferInputs (input : Inputs) : Inputs := { input with family := 1 }

def nativeModel {T : Type} (model : Model T ActionView) : Model T ActionView :=
  { model with
    fields := fun action => (statement action).fields
    effects := project
    pair := fun action => ⟨action.decodedFields.userRoot, action.decodedFields.assetRoot⟩
    timestamp := fun action => action.decodedFields.timestamp }

/- The complete retained transaction supplies the context anchor, even though
auth/effect encoders inspect its body. The native decoder establishes both outer
wrapper associations constructively, rather than through an associated premise. -/
def contextModel {B : Type} (model : Model (NativeTransaction B) ActionView)
    (decode : List Nat → Option (NativeTransaction B)) : Model (NativeTransaction B) ActionView :=
  { nativeModel model with
    decode := decodeCarrier decode
    extract := fun transaction index =>
      let entry := model.extract transaction index
      { entry with body := { entry.body with contextAnchor := transaction.anchor } } }

theorem transfer_family_fixed (input : Inputs) : (transferInputs input).family = 1 := rfl

theorem native_statement_full64 (action : ActionView) :
    (statement action).fields.length = 64 := TransferStatement.fields_length _

theorem native_projection_exact (action : ActionView) :
    RuntimeTransferStatement.rustProjection (statement action) = (statement action).fields :=
  RuntimeTransferStatement.projection_exact _

theorem context_model_anchor {B : Type} (model : Model (NativeTransaction B) ActionView)
    (decode : List Nat → Option (NativeTransaction B)) (transaction : NativeTransaction B) (index : Nat) :
    (statement ((contextModel model decode).extract transaction index).body).anchor =
      transaction.anchor := rfl

theorem native_context_constructed (action : ActionView) :
    (statement action).anchor = action.contextAnchor ∧
    (statement action).volumeContext = action.context.code := ⟨rfl, rfl⟩

theorem native_effects_from_same_source (action : ActionView) :
    (project action).spend0 = (statement action).firstNullifier ∧
    (project action).spend1 = (statement action).secondNullifier ∧
    (project action).output0.noteCommitment = (statement action).recipientNote ∧
    (project action).output1.noteCommitment = (statement action).changeNote ∧
    (project action).output0.payload = action.recipientPayload ∧
    (project action).output1.payload = action.changePayload ∧
    (project action).volume.day = (statement action).volumeDayStart ∧
    (project action).volume.nullifier = (statement action).volumeNullifier ∧
    (project action).volume.commitment = (statement action).volumeCommitment ∧
    (project action).volume.payload = action.volumePayload := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem native_effect_arity (action : ActionView) :
    [(project action).spend0, (project action).spend1].length = 2 ∧
    [(project action).output0, (project action).output1].length = 2 := ⟨rfl, rfl⟩

theorem native_expected_item {T : Type} (model : Model T ActionView) (input : Inputs)
    (crypto : TransferSem.Crypto) (carrier : TransferNativeSignaturePolicy.Carrier T) (index : Nat) :
    expected (nativeModel model) crypto (transferInputs input).family carrier index =
      ⟨1, crypto.hash .transferStatement (statement (model.extract carrier.body index).body).fields,
        (model.extract carrier.body index).envelope⟩ := rfl

theorem native_current_pair_time {T : Type} (model : Model T ActionView) (action : ActionView) :
    (nativeModel model).pair action =
      ⟨(statement action).userRoot, (statement action).assetRoot⟩ ∧
    (nativeModel model).timestamp action = (statement action).timestamp := ⟨rfl, rfl⟩

theorem native_wrong_body_anchor_refused (action : ActionView)
    (wrong : action.bodyAnchor ≠ action.contextAnchor) :
    ¬ AnchorBound action.bodyAnchor action.contextAnchor (statement action).anchor := by
  intro admitted
  exact wrong admitted.1

theorem native_statement_equivocation (hash : List Nat → Nat) (first second : ActionView)
    (different : statement first ≠ statement second)
    (same : hash (statement first).fields = hash (statement second).fields) :
    (statement first).fields ≠ (statement second).fields ∧
      hash (statement first).fields = hash (statement second).fields :=
  TransferStatement.equivocation_is_collision hash _ _ different same

set_option pp.all true in
#check @native_decoder_context
#print axioms native_decoder_context
set_option pp.all true in
#check @transfer_family_fixed
#print axioms transfer_family_fixed
set_option pp.all true in
#check @native_statement_full64
#print axioms native_statement_full64
set_option pp.all true in
#check @native_projection_exact
#print axioms native_projection_exact
set_option pp.all true in
#check @context_model_anchor
#print axioms context_model_anchor
set_option pp.all true in
#check @native_context_constructed
#print axioms native_context_constructed
set_option pp.all true in
#check @native_effects_from_same_source
#print axioms native_effects_from_same_source
set_option pp.all true in
#check @native_effect_arity
#print axioms native_effect_arity
set_option pp.all true in
#check @native_expected_item
#print axioms native_expected_item
set_option pp.all true in
#check @native_current_pair_time
#print axioms native_current_pair_time
set_option pp.all true in
#check @native_wrong_body_anchor_refused
#print axioms native_wrong_body_anchor_refused
set_option pp.all true in
#check @native_statement_equivocation
#print axioms native_statement_equivocation

end ShielddSecurity.TransferNativeCarrierBridge
