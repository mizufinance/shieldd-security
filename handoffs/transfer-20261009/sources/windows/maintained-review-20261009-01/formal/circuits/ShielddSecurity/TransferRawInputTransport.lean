import ShielddSecurity.TransferAuthorizationBranchCompletion
import ShielddSecurity.TransferSpendBranchCompletion
import ShielddSecurity.TransferRegistryUserCompletion

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-! Transport raw construction prerequisites using only the fields read by
the owned algorithms. Other computed storage may still be zero in an earlier
stage. No semantic result or row satisfaction is supplied by these frames. -/
namespace ShielddSecurity.TransferRawInputTransport
open TransferCore TransferSem

structure AuthorizationFrame (base old : TransferSem.Witness) : Prop where
  asset : base.asset = old.asset
  regulated : base.regulated = old.regulated
  registry : base.registry = old.registry
  senderAddress : base.sender.address = old.sender.address
  senderDH : base.sender.rnkDH = old.sender.rnkDH
  senderCommitment : base.sender.rnkCommitment = old.sender.rnkCommitment

theorem authorization_inputs_transport (c : Crypto) (base old : TransferSem.Witness)
    (frame : AuthorizationFrame base old) (i : TransferAuthorizationBranchCompletion.RawInputs)
    (legal : TransferAuthorizationBranchCompletion.LegalInputs c old i) :
    TransferAuthorizationBranchCompletion.LegalInputs c base i := by
  refine ⟨legal.akValid, legal.akNonidentity, legal.nkCanonical, legal.randomizerBounded,
    ?_, ?_, legal.ivkNonzero, ?_, ?_, legal.rkNonidentity⟩
  · rw [frame.asset]
    exact legal.assetNonzero
  · simpa only [ring, frame.regulated, frame.registry] using legal.ringNonidentity
  · rw [frame.senderAddress]
    exact legal.owner
  · rw [frame.senderDH]
    exact legal.rnkDHNonidentity

theorem authorization_owned_fields (c : Crypto) (base old : TransferSem.Witness)
    (frame : AuthorizationFrame base old) (i : TransferAuthorizationBranchCompletion.RawInputs) :
    (TransferAuthorizationBranchCompletion.construct c base i).auth =
        (TransferAuthorizationBranchCompletion.construct c old i).auth ∧
      (TransferAuthorizationBranchCompletion.construct c base i).sender.rnkCommitment =
        (TransferAuthorizationBranchCompletion.construct c old i).sender.rnkCommitment := by
  constructor
  · rfl
  · simp only [TransferAuthorizationBranchCompletion.construct,
      TransferAuthorizationBranchCompletion.senderCommitment,
      TransferAuthorizationBranchCompletion.provisional, rnk, ring,
      frame.asset, frame.regulated, frame.registry, frame.senderAddress,
      frame.senderDH, frame.senderCommitment]

structure SpendFrame (base old : TransferSem.Witness) : Prop extends AuthorizationFrame base old where
  anchor : base.anchor = old.anchor
  authorization : base.auth = old.auth
  optionalDummy : base.optionalDummy = old.optionalDummy
  paddingSeed : base.paddingSeed = old.paddingSeed

def transportSpends (c : Crypto) (base old : TransferSem.Witness)
    (frame : SpendFrame base old) (i : TransferSpendBranchCompletion.LegalInputs c old) :
    TransferSpendBranchCompletion.LegalInputs c base where
  raw := i.raw
  amountBounded := i.amountBounded
  positionBounded := i.positionBounded
  blindingCanonical := i.blindingCanonical
  recoveryCanonical := i.recoveryCanonical
  pathCanonical := i.pathCanonical
  dummyAmount := by
    intro slot dummy
    apply i.dummyAmount slot
    simpa only [TransferSpendBranchCompletion.isDummy, frame.optionalDummy] using dummy
  authenticated := by
    intro slot real
    have original : ¬ TransferSpendBranchCompletion.isDummy old slot := by
      simpa only [TransferSpendBranchCompletion.isDummy, frame.optionalDummy] using real
    simpa only [TransferSpendBranchCompletion.commitment, frame.asset,
      frame.senderAddress, frame.anchor] using i.authenticated slot original

theorem spend_inputs_transport (c : Crypto) (base old : TransferSem.Witness)
    (frame : SpendFrame base old) (i : TransferSpendBranchCompletion.LegalInputs c old) :
    (transportSpends c base old frame i).raw = i.raw := rfl

theorem spend_owned_records (c : Crypto) (base old : TransferSem.Witness)
    (frame : SpendFrame base old) (i : TransferSpendBranchCompletion.LegalInputs c old)
    (slot : Fin 2) :
    (TransferSpendBranchCompletion.construct c base (transportSpends c base old frame i)).spends slot =
      (TransferSpendBranchCompletion.construct c old i).spends slot := by
  simp only [TransferSpendBranchCompletion.construct, TransferSpendBranchCompletion.constructSpend,
    transportSpends, TransferSpendBranchCompletion.nullifier,
    TransferSpendBranchCompletion.isDummy, TransferSpendBranchCompletion.commitment,
    effectiveNK, rnk, ring, frame.asset, frame.regulated, frame.registry,
    frame.senderAddress, frame.senderDH, frame.authorization, frame.optionalDummy, frame.paddingSeed]

structure UserFrame (base old : TransferSem.Witness) (user original : User) : Prop where
  asset : base.asset = old.asset
  regulated : base.regulated = old.regulated
  userAnchor : base.userAnchor = old.userAnchor
  address : user.address = original.address
  dh : user.rnkDH = original.rnkDH
  commitment : user.rnkCommitment = original.rnkCommitment

theorem user_path_transport (c : Crypto) (base old : TransferSem.Witness) (user original : User)
    (frame : UserFrame base old user original) (i : TransferRegistryUserCompletion.UserPathInputs)
    (legal : TransferRegistryUserCompletion.LegalUserPath c old original i) :
    TransferRegistryUserCompletion.LegalUserPath c base user i := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, legal.generationBounded, legal.inactiveLifecycleBounded,
    legal.positionBounded, legal.siblingsCanonical, ?_⟩
  · rw [frame.address]
    exact legal.diversifiedValid
  · rw [frame.address]
    exact legal.diversifiedNonidentity
  · rw [frame.address]
    exact legal.transmissionValid
  · rw [frame.address]
    exact legal.transmissionNonidentity
  · rw [frame.dh]
    exact legal.rnkDHValid
  · rw [frame.dh]
    exact legal.rnkDHNonidentity
  · intro enabled
    have originalEnabled : old.regulated = true := frame.regulated.symm.trans enabled
    simpa only [TransferRegistryUserCompletion.constructUser, userLeaf,
      frame.asset, frame.regulated, frame.userAnchor, frame.address, frame.dh,
      frame.commitment] using legal.authenticated originalEnabled

set_option pp.all true in
#check @authorization_inputs_transport
#print axioms authorization_inputs_transport
set_option pp.all true in
#check @authorization_owned_fields
#print axioms authorization_owned_fields
set_option pp.all true in
#check @spend_inputs_transport
#print axioms spend_inputs_transport
set_option pp.all true in
#check @spend_owned_records
#print axioms spend_owned_records
set_option pp.all true in
#check @user_path_transport
#print axioms user_path_transport

end ShielddSecurity.TransferRawInputTransport
