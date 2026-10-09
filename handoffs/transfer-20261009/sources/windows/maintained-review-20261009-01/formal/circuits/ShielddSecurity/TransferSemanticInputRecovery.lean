import ShielddSecurity.TransferTailRawInputRecovery
import ShielddSecurity.TransferSemanticConstruction

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

/-! Inverse coverage of the actual ordered raw semantic input interface.
The independent semantic predicate is consumed in this reverse direction.
Full circuit assignment and correspondence with Rust remain separate claims. -/
namespace ShielddSecurity.TransferSemanticInputRecovery
open TransferCore TransferSem

def recover (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferSemanticConstruction.Inputs c where
  initial := TransferInitialWitnessDecomposition.recover w
  initialLegal := TransferInitialWitnessDecomposition.recovered_inputs_legal c w legal
  registry := TransferEarlierInputRecovery.registryInputs c w legal
  authorization := TransferAuthorizationDecomposition.recover w
  authorizationLegal := TransferEarlierInputRecovery.authorization_inputs_legal c w legal
  spends := TransferEarlierInputRecovery.spendInputs c w legal
  sender := TransferEarlierUserRecovery.senderInputs w
  receiver := TransferEarlierUserRecovery.receiverInputs w
  senderLegal := TransferEarlierUserRecovery.sender_inputs_legal c w legal
  receiverLegal := TransferEarlierUserRecovery.receiver_inputs_legal c w legal
  tail := TransferTailRawInputRecovery.recover c w zeroMul legal
  assetGeneratorNonidentity := by
    change nonidentity (c.assetGenerator (TransferEarlierInputRecovery.registryStage c w legal).asset)
    rw [(TransferEarlierInputRecovery.registry_frame c w legal).asset]
    rcases legal.2.1 with ⟨_, _, _, _, _, _, _, _, _, balance⟩
    exact balance.2

theorem constructed_stage_agrees (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    TransferSemanticConstruction.construct c (recover c w zeroMul legal) =
      TransferTailEncryptionRecovery.finalStage c w zeroMul legal := rfl

theorem public_fields_preserved (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    publicFields c (TransferSemanticConstruction.construct c (recover c w zeroMul legal)) =
      publicFields c w := by
  rw [constructed_stage_agrees, TransferTailEncryptionRecovery.normalized_record]
  have encryption := TransferEncryptionDecomposition.agreement_all64 c
    { w with
      volume := TransferVolumeBranchCompletion.construct c w
        (TransferTailOutputRecovery.originalVolumeInputs c w legal) }
    (TransferEncryptionBranchCompletion.construct c w
      (TransferTailEncryptionRecovery.originalEncryptionInputs c w zeroMul legal))
    (TransferEncryptionDecomposition.recovered_public_agreement c w zeroMul
      legal.2.1.2.2.2.2.2.2.2.2.1 legal.1)
  exact encryption.trans (TransferVolumeDecomposition.full_public_statement_preserved c w
    legal.2.1.2.2.2.2.2.2.1
    (Nat.pos_of_ne_zero ((legal.2.1.2.2.2.2.2.1 0).2.1 rfl))
    (legal.2.1.2.2.2.2.2.1 0).1)

private theorem constructed_blinding (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    (TransferSemanticConstruction.construct c (recover c w zeroMul legal)).blinding = w.blinding := by
  have headers := TransferSemanticConstruction.raw_headers_and_selector_preserved c
    (recover c w zeroMul legal)
  exact headers.2.2.2.2.2.1

theorem relation_inputs_preserved (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    c.hash .transferStatement
      (publicFields c (TransferSemanticConstruction.construct c (recover c w zeroMul legal))) =
        c.hash .transferStatement (publicFields c w) ∧
      (TransferSemanticConstruction.construct c (recover c w zeroMul legal)).blinding = w.blinding :=
  ⟨congrArg (c.hash .transferStatement) (public_fields_preserved c w zeroMul legal),
    constructed_blinding c w zeroMul legal⟩

theorem ordered_raw_inputs_exist (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w) :
    ∃ i : TransferSemanticConstruction.Inputs c,
      publicFields c (TransferSemanticConstruction.construct c i) = publicFields c w ∧
        (TransferSemanticConstruction.construct c i).blinding = w.blinding :=
  ⟨recover c w zeroMul legal, public_fields_preserved c w zeroMul legal,
    constructed_blinding c w zeroMul legal⟩

theorem recovered_constructed_semantics (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c) (legal : TransferSem.TransferSem c w)
    (cryptoCanonical : CanonicalCrypto c) (group : TransferAuthorizationBranchCompletion.GroupClosure c) :
    TransferSem.TransferSem c (TransferSemanticConstruction.construct c (recover c w zeroMul legal)) :=
  TransferSemanticConstruction.constructed_transfer_semantics c (recover c w zeroMul legal)
    cryptoCanonical group

set_option pp.all true in
#check @constructed_stage_agrees
#print axioms constructed_stage_agrees
set_option pp.all true in
#check @public_fields_preserved
#print axioms public_fields_preserved
set_option pp.all true in
#check @relation_inputs_preserved
#print axioms relation_inputs_preserved
set_option pp.all true in
#check @ordered_raw_inputs_exist
#print axioms ordered_raw_inputs_exist
set_option pp.all true in
#check @recovered_constructed_semantics
#print axioms recovered_constructed_semantics

end ShielddSecurity.TransferSemanticInputRecovery
