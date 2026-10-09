import ShielddSecurity.TransferEarlierUserRecovery
import ShielddSecurity.TransferTailInputTransport

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferTailOutputRecovery
open TransferCore TransferSem

def outputInputs (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferOutputRecoveryCompletion.LegalOutputInputs c :=
  TransferOutputDecomposition.recoverInputs c w legal.2.1.2.2.2.2.2.1

def outputStage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  TransferSemanticTailConstruction.outputStage c (TransferEarlierUserRecovery.earlierStage c w legal)
    (outputInputs c w legal)

theorem output_records_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) : (outputStage c w legal).outputs = w.outputs := by
  have frame : TransferOutputRecoveryCompletion.constructOutputs c
      { TransferEarlierUserRecovery.earlierStage c w legal with
        outputs := w.outputs
        volume := w.volume
        routing := w.routing
        encryption := w.encryption } (outputInputs c w legal) =
      TransferOutputRecoveryCompletion.constructOutputs c
        (TransferEarlierUserRecovery.earlierStage c w legal) (outputInputs c w legal) := rfl
  rw [TransferEarlierUserRecovery.earlier_tail_restored c w legal] at frame
  exact frame.symm.trans (TransferOutputDecomposition.outputs_reconstructed c w legal.2.1.2.2.2.2.2.1)

theorem after_outputs_restored (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) :
    { outputStage c w legal with
      volume := w.volume
      routing := w.routing
      encryption := w.encryption } = w := by
  change { TransferEarlierUserRecovery.earlierStage c w legal with
    outputs := (outputStage c w legal).outputs
    volume := w.volume
    routing := w.routing
    encryption := w.encryption } = w
  rw [output_records_reconstructed c w legal]
  exact TransferEarlierUserRecovery.earlier_tail_restored c w legal

theorem output_frame (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferTailInputTransport.Frame (outputStage c w legal) w := by
  have frame := after_outputs_restored c w legal
  exact ⟨by simpa only using congrArg TransferSem.Witness.anchor frame,
    by simpa only using congrArg TransferSem.Witness.asset frame,
    by simpa only using congrArg TransferSem.Witness.regulated frame,
    by simpa only using congrArg TransferSem.Witness.registry frame,
    by simpa only using congrArg TransferSem.Witness.sender frame,
    by simpa only using congrArg TransferSem.Witness.receiver frame,
    by simpa only using congrArg TransferSem.Witness.outputs frame,
    by simpa only using congrArg TransferSem.Witness.auth frame,
    by simpa only using congrArg TransferSem.Witness.timestamp frame,
    by simpa only using congrArg TransferSem.Witness.nonce frame⟩

def originalVolumeInputs (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferVolumeBranchCompletion.LegalVolumeInputs c w :=
  TransferVolumeDecomposition.recoverInputs c w legal.2.1.2.2.2.2.2.2.1
    (Nat.pos_of_ne_zero ((legal.2.1.2.2.2.2.2.1 0).2.1 rfl)) (legal.2.1.2.2.2.2.2.1 0).1

def volumeInputs (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferVolumeBranchCompletion.LegalVolumeInputs c (outputStage c w legal) :=
  TransferTailInputTransport.transportVolume c (outputStage c w legal) w (output_frame c w legal)
    (originalVolumeInputs c w legal)

def volumeStage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  TransferSemanticTailConstruction.volumeStage c (TransferEarlierUserRecovery.earlierStage c w legal)
    (outputInputs c w legal) (volumeInputs c w legal)

theorem volume_record_agrees (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    (volumeStage c w legal).volume =
      TransferVolumeBranchCompletion.construct c w (originalVolumeInputs c w legal) :=
  TransferTailInputTransport.volume_construct_agrees c (outputStage c w legal) w (output_frame c w legal)
    (originalVolumeInputs c w legal)

theorem volume_encryption_frame (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferTailInputTransport.EncryptionFrame (volumeStage c w legal) w := by
  have frame := output_frame c w legal
  exact ⟨⟨frame.anchor, frame.asset, frame.regulated, frame.registry, frame.sender, frame.receiver,
    frame.outputs, frame.authorization, frame.timestamp, frame.nonce⟩, rfl, rfl⟩

set_option pp.all true in
#check @output_records_reconstructed
#print axioms output_records_reconstructed
set_option pp.all true in
#check @after_outputs_restored
#print axioms after_outputs_restored
set_option pp.all true in
#check @output_frame
#print axioms output_frame
set_option pp.all true in
#check @volume_record_agrees
#print axioms volume_record_agrees
set_option pp.all true in
#check @volume_encryption_frame
#print axioms volume_encryption_frame

end ShielddSecurity.TransferTailOutputRecovery
