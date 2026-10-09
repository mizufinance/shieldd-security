import ShielddSecurity.TransferCanonicalDecomposition
import ShielddSecurity.TransferInitialWitnessDecomposition
import ShielddSecurity.TransferRegistryDecomposition
import ShielddSecurity.TransferAuthorizationDecomposition
import ShielddSecurity.TransferSpendDecomposition
import ShielddSecurity.TransferOutputDecomposition
import ShielddSecurity.TransferUserLifecycleDecomposition
import ShielddSecurity.TransferVolumeDecomposition
import ShielddSecurity.TransferEncryptionDecomposition
import ShielddSecurity.TransferRoutingDecomposition

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

/-! Joint reverse coverage at one independently legal semantic frame. This
record packages every component's raw input domain. It is not the sequential
TransferSemanticConstruction.Inputs record: transport between those stages,
one total circuit assignment, and all-row satisfaction remain separate work. -/
namespace ShielddSecurity.TransferRawInputCoverage
open TransferCore TransferSem

structure InputsAt (c : Crypto) (w : TransferSem.Witness) where
  initial : TransferInitialWitnessConstruction.Inputs
  initialLegal : TransferInitialWitnessConstruction.Legal initial
  registry : TransferRegistryUserCompletion.RegistryInputs c w
  authorization : TransferAuthorizationBranchCompletion.RawInputs
  authorizationLegal : TransferAuthorizationBranchCompletion.LegalInputs c w authorization
  spends : TransferSpendBranchCompletion.LegalInputs c w
  outputs : TransferOutputRecoveryCompletion.LegalOutputInputs c
  sender : TransferRegistryUserCompletion.UserPathInputs
  receiver : TransferRegistryUserCompletion.UserPathInputs
  senderLegal : TransferRegistryUserCompletion.LegalUserPath c w w.sender sender
  receiverLegal : TransferRegistryUserCompletion.LegalUserPath c w w.receiver receiver
  volume : TransferVolumeBranchCompletion.LegalVolumeInputs c w
  encryption : TransferEncryptionBranchCompletion.LegalEncryptionInputs c w
  routing : TransferRoutingBranchCompletion.LegalRoutingInputs

def recover (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) : InputsAt c w where
  initial := TransferInitialWitnessDecomposition.recover w
  initialLegal := TransferInitialWitnessDecomposition.recovered_inputs_legal c w legal
  registry := TransferRegistryDecomposition.recoverInputs c w legal.2.1.1
    (TransferCanonicalDecomposition.registry_fields_canonical w legal.1)
  authorization := TransferAuthorizationDecomposition.recover w
  authorizationLegal := TransferAuthorizationDecomposition.recovered_inputs_legal c w
    legal.2.1.2.2.2.1 (TransferCanonicalDecomposition.authorization_scalars_canonical w legal.1).1
  spends := TransferSpendDecomposition.recoverInputs c w legal.2.1.2.2.2.2.1
    (fun slot => (TransferCanonicalDecomposition.note_fields_canonical w legal.1 slot).1)
  outputs := TransferOutputDecomposition.recoverInputs c w legal.2.1.2.2.2.2.2.1
  sender := TransferUserLifecycleDecomposition.recoverLegalPath w.regulated w.sender
  receiver := TransferUserLifecycleDecomposition.recoverLegalPath w.regulated w.receiver
  senderLegal := (TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.sender
    legal.2.1.2.1 (TransferCanonicalDecomposition.user_fields_canonical w legal.1).1).1
  receiverLegal := (TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.receiver
    legal.2.1.2.2.1 (TransferCanonicalDecomposition.user_fields_canonical w legal.1).2).1
  volume := TransferVolumeDecomposition.recoverInputs c w legal.2.1.2.2.2.2.2.2.1
    (Nat.pos_of_ne_zero ((legal.2.1.2.2.2.2.2.1 0).2.1 rfl))
    (legal.2.1.2.2.2.2.2.1 0).1
  encryption := TransferEncryptionDecomposition.recover c w zeroMul legal.2.1.2.2.2.2.2.2.2.2.1
  routing := TransferRoutingDecomposition.recoverInputs c w legal.2.1.2.2.2.2.2.2.2.1

theorem inputs_exist (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) : Nonempty (InputsAt c w) :=
  ⟨recover c w zeroMul legal⟩

theorem fixed_headers (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) :
    (recover c w zeroMul legal).initial.anchor = w.anchor ∧
      (recover c w zeroMul legal).initial.blinding = w.blinding ∧
      (recover c w zeroMul legal).initial.optionalDummy = w.optionalDummy :=
  ⟨rfl, rfl, rfl⟩

theorem registry_and_authorization (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) :
    TransferRegistryUserCompletion.constructRegistry c w (recover c w zeroMul legal).registry = w ∧
      TransferAuthorizationBranchCompletion.construct c w
        (recover c w zeroMul legal).authorization = w :=
  ⟨TransferRegistryDecomposition.full_record_reconstructed c w legal.2.1.1
      (TransferCanonicalDecomposition.registry_fields_canonical w legal.1),
    TransferAuthorizationDecomposition.full_record_reconstructed c w legal.2.1.2.2.2.1⟩

theorem spends_and_outputs (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) :
    TransferSpendBranchCompletion.construct c w (recover c w zeroMul legal).spends = w ∧
      TransferOutputRecoveryCompletion.constructOutputs c w (recover c w zeroMul legal).outputs = w.outputs :=
  ⟨TransferSpendDecomposition.full_record_reconstructed c w legal.2.1.2.2.2.2.1
      (fun slot => (TransferCanonicalDecomposition.note_fields_canonical w legal.1 slot).1),
    TransferOutputDecomposition.outputs_reconstructed c w legal.2.1.2.2.2.2.2.1⟩

theorem users_and_routing (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) :
    TransferRegistryUserCompletion.constructUser w.regulated w.sender
        (recover c w zeroMul legal).sender = w.sender ∧
      TransferRegistryUserCompletion.constructUser w.regulated w.receiver
        (recover c w zeroMul legal).receiver = w.receiver ∧
      TransferRoutingBranchCompletion.construct c w (recover c w zeroMul legal).routing = w.routing :=
  ⟨(TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.sender
      legal.2.1.2.1 (TransferCanonicalDecomposition.user_fields_canonical w legal.1).1).2,
    (TransferUserLifecycleDecomposition.user_sem_has_legal_raw_path c w w.receiver
      legal.2.1.2.2.1 (TransferCanonicalDecomposition.user_fields_canonical w legal.1).2).2,
    TransferRoutingDecomposition.routing_reconstructed c w legal.2.1.2.2.2.2.2.2.2.1⟩

set_option pp.all true in
#check @inputs_exist
#print axioms inputs_exist
set_option pp.all true in
#check @fixed_headers
#print axioms fixed_headers
set_option pp.all true in
#check @registry_and_authorization
#print axioms registry_and_authorization
set_option pp.all true in
#check @spends_and_outputs
#print axioms spends_and_outputs
set_option pp.all true in
#check @users_and_routing
#print axioms users_and_routing

end ShielddSecurity.TransferRawInputCoverage
