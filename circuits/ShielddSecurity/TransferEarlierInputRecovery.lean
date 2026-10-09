import ShielddSecurity.TransferRawInputCoverage
import ShielddSecurity.TransferRawInputTransport

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

/-! Recover inputs in the actual registry/authorization/spend ordering. Each
frame below is proved from constructed records. It is not an input assumption
that the unfinished stages already equal the final semantic witness. -/
namespace ShielddSecurity.TransferEarlierInputRecovery
open TransferCore TransferSem

def initialStage (w : TransferSem.Witness) : TransferSem.Witness :=
  TransferInitialWitnessConstruction.construct (TransferInitialWitnessDecomposition.recover w)

def registryInputs (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferRegistryUserCompletion.RegistryInputs c (initialStage w) :=
  TransferRegistryDecomposition.recoverAt c (initialStage w) w rfl legal.2.1.1
    (TransferCanonicalDecomposition.registry_fields_canonical w legal.1)

def registryStage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  TransferRegistryUserCompletion.constructRegistry c (initialStage w) (registryInputs c w legal)

theorem registry_frame (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferRawInputTransport.AuthorizationFrame (registryStage c w legal) w := by
  have owned := TransferRegistryDecomposition.recovered_at_owned_fields c (initialStage w) w rfl
    legal.2.1.1 (TransferCanonicalDecomposition.registry_fields_canonical w legal.1)
  exact ⟨owned.2.2, owned.2.1, owned.1, rfl, rfl, rfl⟩

theorem authorization_inputs_legal (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) :
    TransferAuthorizationBranchCompletion.LegalInputs c (registryStage c w legal)
      (TransferAuthorizationDecomposition.recover w) :=
  TransferRawInputTransport.authorization_inputs_transport c (registryStage c w legal) w
    (registry_frame c w legal) (TransferAuthorizationDecomposition.recover w)
    (TransferAuthorizationDecomposition.recovered_inputs_legal c w legal.2.1.2.2.2.1
      (TransferCanonicalDecomposition.authorization_scalars_canonical w legal.1).1)

def authorizationStage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  TransferAuthorizationBranchCompletion.construct c (registryStage c w legal)
    (TransferAuthorizationDecomposition.recover w)

theorem authorization_frame (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) :
    TransferRawInputTransport.SpendFrame (authorizationStage c w legal) w := by
  have frame := registry_frame c w legal
  have owned := TransferRawInputTransport.authorization_owned_fields c (registryStage c w legal) w
    frame (TransferAuthorizationDecomposition.recover w)
  have reconstructed := TransferAuthorizationDecomposition.full_record_reconstructed c w
    legal.2.1.2.2.2.1
  have authorization : (authorizationStage c w legal).auth = w.auth :=
    owned.1.trans (congrArg TransferSem.Witness.auth reconstructed)
  have commitment : (authorizationStage c w legal).sender.rnkCommitment = w.sender.rnkCommitment :=
    owned.2.trans (congrArg (fun record : TransferSem.Witness => record.sender.rnkCommitment) reconstructed)
  exact ⟨⟨frame.asset, frame.regulated, frame.registry, frame.senderAddress, frame.senderDH, commitment⟩,
    rfl, authorization, rfl, rfl⟩

def originalSpendInputs (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSpendBranchCompletion.LegalInputs c w :=
  TransferSpendDecomposition.recoverInputs c w legal.2.1.2.2.2.2.1
    (fun slot => (TransferCanonicalDecomposition.note_fields_canonical w legal.1 slot).1)

def spendInputs (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSpendBranchCompletion.LegalInputs c (authorizationStage c w legal) :=
  TransferRawInputTransport.transportSpends c (authorizationStage c w legal) w
    (authorization_frame c w legal) (originalSpendInputs c w legal)

def spendStage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSem.Witness :=
  TransferSpendBranchCompletion.construct c (authorizationStage c w legal) (spendInputs c w legal)

theorem spend_records_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) : (spendStage c w legal).spends = w.spends := by
  have reconstructed := TransferSpendDecomposition.full_record_reconstructed c w
    legal.2.1.2.2.2.2.1
    (fun slot => (TransferCanonicalDecomposition.note_fields_canonical w legal.1 slot).1)
  funext slot
  exact (TransferRawInputTransport.spend_owned_records c (authorizationStage c w legal) w
    (authorization_frame c w legal) (originalSpendInputs c w legal) slot).trans
      (congrArg (fun record : TransferSem.Witness => record.spends slot) reconstructed)

theorem user_frames (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferRawInputTransport.UserFrame (spendStage c w legal) w (spendStage c w legal).sender w.sender ∧
      TransferRawInputTransport.UserFrame (spendStage c w legal) w (spendStage c w legal).receiver w.receiver := by
  have frame := authorization_frame c w legal
  exact ⟨⟨frame.asset, frame.regulated, rfl, frame.senderAddress, frame.senderDH, frame.senderCommitment⟩,
    ⟨frame.asset, frame.regulated, rfl, rfl, rfl, rfl⟩⟩

set_option pp.all true in
#check @registry_frame
#print axioms registry_frame
set_option pp.all true in
#check @authorization_inputs_legal
#print axioms authorization_inputs_legal
set_option pp.all true in
#check @authorization_frame
#print axioms authorization_frame
set_option pp.all true in
#check @spend_records_reconstructed
#print axioms spend_records_reconstructed
set_option pp.all true in
#check @user_frames
#print axioms user_frames

end ShielddSecurity.TransferEarlierInputRecovery
