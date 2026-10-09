import ShielddSecurity.TransferEarlierInputRecovery
import ShielddSecurity.TransferSemanticTailConstruction

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEarlierUserRecovery
open TransferCore TransferSem TransferEarlierInputRecovery

def senderInputs (w : TransferSem.Witness) : TransferRegistryUserCompletion.UserPathInputs :=
  TransferUserLifecycleDecomposition.recoverLegalPath w.regulated w.sender

def receiverInputs (w : TransferSem.Witness) : TransferRegistryUserCompletion.UserPathInputs :=
  TransferUserLifecycleDecomposition.recoverLegalPath w.regulated w.receiver

theorem sender_inputs_legal (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferRegistryUserCompletion.LegalUserPath c (spendStage c w legal)
      (spendStage c w legal).sender (senderInputs w) :=
  TransferRawInputTransport.user_path_transport c (spendStage c w legal) w
    (spendStage c w legal).sender w.sender (user_frames c w legal).1 (senderInputs w)
    (TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.sender legal.2.1.2.1
      (TransferCanonicalDecomposition.user_fields_canonical w legal.1).1).1

theorem receiver_inputs_legal (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferRegistryUserCompletion.LegalUserPath c (spendStage c w legal)
      (spendStage c w legal).receiver (receiverInputs w) :=
  TransferRawInputTransport.user_path_transport c (spendStage c w legal) w
    (spendStage c w legal).receiver w.receiver (user_frames c w legal).2 (receiverInputs w)
    (TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.receiver legal.2.1.2.2.1
      (TransferCanonicalDecomposition.user_fields_canonical w legal.1).2).1

def earlierStage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  TransferRegistryUserCompletion.constructUsers (spendStage c w legal) (senderInputs w) (receiverInputs w)

private theorem user_construct_agrees (base old : TransferSem.Witness) (user original : User)
    (frame : TransferRawInputTransport.UserFrame base old user original)
    (i : TransferRegistryUserCompletion.UserPathInputs) :
    TransferRegistryUserCompletion.constructUser base.regulated user i =
      TransferRegistryUserCompletion.constructUser old.regulated original i := by
  simp only [TransferRegistryUserCompletion.constructUser, frame.regulated,
    frame.address, frame.dh, frame.commitment]

theorem user_records_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) :
    (earlierStage c w legal).sender = w.sender ∧ (earlierStage c w legal).receiver = w.receiver := by
  have frames := user_frames c w legal
  exact ⟨(user_construct_agrees (spendStage c w legal) w (spendStage c w legal).sender w.sender
      frames.1 (senderInputs w)).trans
      (TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.sender legal.2.1.2.1
        (TransferCanonicalDecomposition.user_fields_canonical w legal.1).1).2,
    (user_construct_agrees (spendStage c w legal) w (spendStage c w legal).receiver w.receiver
      frames.2 (receiverInputs w)).trans
      (TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.receiver legal.2.1.2.2.1
        (TransferCanonicalDecomposition.user_fields_canonical w legal.1).2).2⟩

/-! All earlier fields are now reconstructed from raw inputs. Restoring the
still-unconstructed tail gives the original witness. This is a record-frame
theorem; no row assignment is asserted. -/
theorem earlier_tail_restored (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    { earlierStage c w legal with
      outputs := w.outputs
      volume := w.volume
      routing := w.routing
      encryption := w.encryption } = w := by
  have users := user_records_reconstructed c w legal
  have registry := registry_frame c w legal
  have authorization := authorization_frame c w legal
  have spends := spend_records_reconstructed c w legal
  change { earlierStage c w legal with
    sender := (earlierStage c w legal).sender
    receiver := (earlierStage c w legal).receiver
    outputs := w.outputs
    volume := w.volume
    routing := w.routing
    encryption := w.encryption } = w
  rw [users.1, users.2]
  change { w with
    asset := (registryStage c w legal).asset
    regulated := (registryStage c w legal).regulated
    registry := (registryStage c w legal).registry
    auth := (authorizationStage c w legal).auth
    spends := (spendStage c w legal).spends } = w
  rw [registry.asset, registry.regulated, registry.registry, authorization.authorization, spends]

theorem earlier_components_recovered (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) :
    TransferSemanticTailConstruction.EarlierComponents c (earlierStage c w legal) := by
  have old : TransferSemanticTailConstruction.EarlierComponents c w :=
    ⟨legal.2.1.1, legal.2.1.2.1, legal.2.1.2.2.1, legal.2.1.2.2.2.1, legal.2.1.2.2.2.2.1⟩
  have frame : TransferSemanticTailConstruction.EarlierComponents c
      { earlierStage c w legal with
        outputs := w.outputs
        volume := w.volume
        routing := w.routing
        encryption := w.encryption } =
      TransferSemanticTailConstruction.EarlierComponents c (earlierStage c w legal) := rfl
  rw [earlier_tail_restored c w legal] at frame
  exact frame ▸ old

set_option pp.all true in
#check @sender_inputs_legal
#print axioms sender_inputs_legal
set_option pp.all true in
#check @receiver_inputs_legal
#print axioms receiver_inputs_legal
set_option pp.all true in
#check @user_records_reconstructed
#print axioms user_records_reconstructed
set_option pp.all true in
#check @earlier_tail_restored
#print axioms earlier_tail_restored
set_option pp.all true in
#check @earlier_components_recovered
#print axioms earlier_components_recovered

end ShielddSecurity.TransferEarlierUserRecovery
