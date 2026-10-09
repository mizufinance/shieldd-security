import ShielddSecurity.TransferTailOutputRecovery

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferTailEncryptionRecovery
open TransferCore TransferSem TransferTailOutputRecovery

def originalEncryptionInputs (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferEncryptionBranchCompletion.LegalEncryptionInputs c w :=
  TransferEncryptionDecomposition.recover c w zeroMul legal.2.1.2.2.2.2.2.2.2.2.1

def encryptionInputs (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferEncryptionBranchCompletion.LegalEncryptionInputs c (volumeStage c w legal) :=
  TransferTailInputTransport.transportEncryption c (volumeStage c w legal) w
    (volume_encryption_frame c w legal) (originalEncryptionInputs c w zeroMul legal)

def encryptionStage (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  TransferSemanticTailConstruction.encryptionStage c (TransferEarlierUserRecovery.earlierStage c w legal)
    (outputInputs c w legal) (volumeInputs c w legal) (encryptionInputs c w zeroMul legal)

theorem encryption_record_agrees (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    (encryptionStage c w zeroMul legal).encryption =
      TransferEncryptionBranchCompletion.construct c w (originalEncryptionInputs c w zeroMul legal) :=
  TransferTailInputTransport.encryption_construct_agrees c (volumeStage c w legal) w
    (volume_encryption_frame c w legal) (originalEncryptionInputs c w zeroMul legal)

theorem encryption_frame (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferTailInputTransport.Frame (encryptionStage c w zeroMul legal) w := by
  have frame := (volume_encryption_frame c w legal).toFrame
  exact ⟨frame.anchor, frame.asset, frame.regulated, frame.registry, frame.sender, frame.receiver,
    frame.outputs, frame.authorization, frame.timestamp, frame.nonce⟩

def routingInputs (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferRoutingBranchCompletion.LegalRoutingInputs :=
  TransferRoutingDecomposition.recoverInputs c w legal.2.1.2.2.2.2.2.2.2.1

def finalStage (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  { encryptionStage c w zeroMul legal with
    routing := TransferRoutingBranchCompletion.construct c
      (encryptionStage c w zeroMul legal) (routingInputs c w legal) }

theorem routing_records_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    (finalStage c w zeroMul legal).routing = w.routing :=
  (TransferTailInputTransport.routing_construct_agrees c (encryptionStage c w zeroMul legal) w
    (encryption_frame c w zeroMul legal) (routingInputs c w legal)).trans
      (TransferRoutingDecomposition.routing_reconstructed c w legal.2.1.2.2.2.2.2.2.2.1)

theorem tail_frame_restored (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    { finalStage c w zeroMul legal with
      volume := w.volume
      encryption := w.encryption } = w := by
  change { outputStage c w legal with
    volume := w.volume
    routing := (finalStage c w zeroMul legal).routing
    encryption := w.encryption } = w
  rw [routing_records_reconstructed c w zeroMul legal]
  exact after_outputs_restored c w legal

theorem normalized_record (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    finalStage c w zeroMul legal =
      { w with
        volume := TransferVolumeBranchCompletion.construct c w (originalVolumeInputs c w legal)
        encryption := TransferEncryptionBranchCompletion.construct c w
          (originalEncryptionInputs c w zeroMul legal) } := by
  have frame := congrArg (fun record : TransferSem.Witness =>
    { record with
      volume := (finalStage c w zeroMul legal).volume
      encryption := (finalStage c w zeroMul legal).encryption })
    (tail_frame_restored c w zeroMul legal)
  change finalStage c w zeroMul legal =
    { w with
      volume := (volumeStage c w legal).volume
      encryption := (encryptionStage c w zeroMul legal).encryption } at frame
  rw [volume_record_agrees c w legal, encryption_record_agrees c w zeroMul legal] at frame
  exact frame

set_option pp.all true in
#check @encryption_record_agrees
#print axioms encryption_record_agrees
set_option pp.all true in
#check @encryption_frame
#print axioms encryption_frame
set_option pp.all true in
#check @routing_records_reconstructed
#print axioms routing_records_reconstructed
set_option pp.all true in
#check @tail_frame_restored
#print axioms tail_frame_restored
set_option pp.all true in
#check @normalized_record
#print axioms normalized_record

end ShielddSecurity.TransferTailEncryptionRecovery
