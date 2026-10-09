import ShielddSecurity.TransferNativeStatementSequence
import ShielddSecurity.TransferNativeSourceCatalogue

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferNativeStatementCatalogue

open TransferNativeCarrierBridge TransferNativeSourceCatalogue TransferSourceBridge TransferProjection

/-! Explicit instantiation of the catalogue source body from the independently
nested encoder source. This retains complete canonical action bytes, signature,
proof envelope and whole payloads alongside the sequence. Actual Rust decoding
and canonical encoders must still establish the source record; no digest inverse,
hash injectivity or desired proof/effect consequence supplies its fields. -/

structure NativeTransfer where
  fields : TransferNativeStatementSequence.Source Nat
  bodyAnchor : Nat
  context : Context
  recipientPayload : Nat
  changePayload : Nat
  volumePayload : Nat
  key : Nat
  signature : List Nat
  envelope : List Nat
  route : Nat
  canonicalActionBytes : List Nat

def publicSource (anchor : Nat) (native : NativeTransfer) : TransferNativeStatementSequence.Source Nat :=
  { native.fields with anchor := anchor, volume := { native.fields.volume with context := native.context.code } }

def fromNative (slot : Slot) (native : NativeTransfer) : TransferSource :=
  { source := { location := slot
                body := { decodedFields := TransferNativeStatementSequence.semantic native.fields
                          contextAnchor := native.fields.anchor
                          bodyAnchor := native.bodyAnchor
                          context := native.context
                          recipientPayload := native.recipientPayload
                          changePayload := native.changePayload
                          volumePayload := native.volumePayload }
                route := native.route
                envelope := native.envelope }
    key := native.key
    signature := native.signature
    canonicalActionBytes := native.canonicalActionBytes }

theorem actual_item_sequence (crypto : TransferSem.Crypto) (anchor : Nat)
    (slot : Slot) (native : NativeTransfer) :
    TransferNativeMixedJoin.actualItem crypto anchor (fromNative slot native).source =
      ⟨1, crypto.hash .transferStatement (TransferNativeStatementSequence.rustFields (publicSource anchor native)),
        native.envelope⟩ := by
  rw [TransferNativeStatementSequence.source_sequence_exact]
  rfl

theorem retained_source_arguments (slot : Slot) (native : NativeTransfer) :
    (fromNative slot native).key = native.key ∧
    (fromNative slot native).signature = native.signature ∧
    (fromNative slot native).canonicalActionBytes = native.canonicalActionBytes ∧
    (fromNative slot native).source.route = native.route ∧
    (fromNative slot native).source.body.bodyAnchor = native.bodyAnchor ∧
    (fromNative slot native).source.body.context = native.context ∧
    (fromNative slot native).source.body.recipientPayload = native.recipientPayload ∧
    (fromNative slot native).source.body.changePayload = native.changePayload ∧
    (fromNative slot native).source.body.volumePayload = native.volumePayload :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem body_catalogue_sequence
    (base : TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView)
    (decode : List Nat → Option (NativeTransaction Body)) (crypto : TransferSem.Crypto)
    (transaction : NativeTransaction Body) (index : Nat) (native : NativeTransfer)
    (inside : (index, fromNative (.bodyAction index) native) ∈ bodyOccurrences 0 transaction.body.actions) :
    TransferFullCarrierAcceptance.expected (contextModel (catalogueModel base) decode) crypto 1
      (carrier transaction) index =
      ⟨1, crypto.hash .transferStatement
        (TransferNativeStatementSequence.rustFields (publicSource transaction.anchor native)), native.envelope⟩ := by
  rw [body_expected_same_source base decode crypto transaction _ inside]
  exact actual_item_sequence crypto transaction.anchor (.bodyAction index) native

theorem fee_catalogue_sequence
    (base : TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView)
    (decode : List Nat → Option (NativeTransaction Body)) (crypto : TransferSem.Crypto)
    (transaction : NativeTransaction Body) (native : NativeTransfer)
    (present : transaction.body.funding = some (fromNative .feeFunding native)) :
    TransferFullCarrierAcceptance.expected (contextModel (catalogueModel base) decode) crypto 1
      (carrier transaction) transaction.body.actions.length =
      ⟨1, crypto.hash .transferStatement
        (TransferNativeStatementSequence.rustFields (publicSource transaction.anchor native)), native.envelope⟩ := by
  rw [fee_expected_same_source base decode crypto transaction _ present]
  exact actual_item_sequence crypto transaction.anchor .feeFunding native

set_option pp.all true in
#check @actual_item_sequence
#print axioms actual_item_sequence
set_option pp.all true in
#check @retained_source_arguments
#print axioms retained_source_arguments
set_option pp.all true in
#check @body_catalogue_sequence
#print axioms body_catalogue_sequence
set_option pp.all true in
#check @fee_catalogue_sequence
#print axioms fee_catalogue_sequence

end ShielddSecurity.TransferNativeStatementCatalogue
