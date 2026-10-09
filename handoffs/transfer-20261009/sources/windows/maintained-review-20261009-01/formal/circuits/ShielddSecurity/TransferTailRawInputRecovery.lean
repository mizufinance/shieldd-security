import ShielddSecurity.TransferTailEncryptionRecovery

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferTailRawInputRecovery
open TransferCore TransferSem TransferTailOutputRecovery TransferTailEncryptionRecovery

theorem output_raw_canonical (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    ∀ slot, ((outputInputs c w legal).raw slot).blinding < fieldModulus ∧
      ((outputInputs c w legal).raw slot).seed < fieldModulus ∧
      ((outputInputs c w legal).raw slot).salt < fieldModulus := by
  change ∀ slot, (w.outputs slot).blinding < fieldModulus ∧
    (w.outputs slot).recovery.seed < fieldModulus ∧ (w.outputs slot).recovery.salt < fieldModulus
  intro slot
  have canonical := (TransferCanonicalDecomposition.note_fields_canonical w legal.1 slot).2
  exact ⟨canonical _ (by simp [outputFields]),
    canonical _ (by simp [outputFields, recoveryFields]),
    canonical _ (by simp [outputFields, recoveryFields])⟩

theorem volume_raw_canonical (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    (volumeInputs c w legal).priorBlinding < fieldModulus ∧
      (volumeInputs c w legal).successorBlinding < fieldModulus ∧
      fieldsCanonical (pathFields (volumeInputs c w legal).priorSiblings) := by
  change w.volume.priorBlinding < fieldModulus ∧ w.volume.successorBlinding < fieldModulus ∧
    fieldsCanonical (pathFields w.volume.priorSiblings)
  have canonical := (TransferCanonicalDecomposition.volume_encryption_fields_canonical w legal.1).1
  refine ⟨canonical _ (by simp [volumeFields]), canonical _ (by simp [volumeFields]), ?_⟩
  intro value member
  exact canonical value (List.mem_append.mpr (Or.inr member))

theorem routing_height_canonical (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    (routingInputs c w legal).height < fieldModulus := by
  change w.routing.height < fieldModulus
  exact legal.1 _ (by simp [CanonicalWitness])

def recover (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferSemanticTailConstruction.Inputs c (TransferEarlierUserRecovery.earlierStage c w legal) where
  output := outputInputs c w legal
  volume := volumeInputs c w legal
  encryption := encryptionInputs c w zeroMul legal
  routing := routingInputs c w legal
  outputBlindingCanonical := fun slot => (output_raw_canonical c w legal slot).1
  outputSeedCanonical := fun slot => (output_raw_canonical c w legal slot).2.1
  outputSaltCanonical := fun slot => (output_raw_canonical c w legal slot).2.2
  priorBlindingCanonical := (volume_raw_canonical c w legal).1
  successorBlindingCanonical := (volume_raw_canonical c w legal).2.1
  priorSiblingsCanonical := (volume_raw_canonical c w legal).2.2
  routingHeightCanonical := routing_height_canonical c w legal

theorem constructed_tail_agrees (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferSemanticTailConstruction.construct c (TransferEarlierUserRecovery.earlierStage c w legal)
      (recover c w zeroMul legal) = finalStage c w zeroMul legal := rfl

theorem legal_tail_inputs_exist (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    ∃ i : TransferSemanticTailConstruction.Inputs c (TransferEarlierUserRecovery.earlierStage c w legal),
      TransferSemanticTailConstruction.construct c (TransferEarlierUserRecovery.earlierStage c w legal) i =
        finalStage c w zeroMul legal :=
  ⟨recover c w zeroMul legal, constructed_tail_agrees c w zeroMul legal⟩

set_option pp.all true in
#check @output_raw_canonical
#print axioms output_raw_canonical
set_option pp.all true in
#check @volume_raw_canonical
#print axioms volume_raw_canonical
set_option pp.all true in
#check @routing_height_canonical
#print axioms routing_height_canonical
set_option pp.all true in
#check @constructed_tail_agrees
#print axioms constructed_tail_agrees
set_option pp.all true in
#check @legal_tail_inputs_exist
#print axioms legal_tail_inputs_exist

end ShielddSecurity.TransferTailRawInputRecovery
