import ShielddSecurity.TransferInitialWitnessConstruction

set_option maxHeartbeats 200000

/-! Recover the raw initial headers and address/key coordinates from an
independently legal semantic witness. The resulting seed deliberately resets
computed storage. This inverse prerequisite is not a complete row assignment
and does not presume the forward constructor's semantic conclusion. -/
namespace ShielddSecurity.TransferInitialWitnessDecomposition

open TransferCore TransferSem TransferInitialWitnessConstruction

def recover (w : TransferSem.Witness) : Inputs where
  anchor := w.anchor
  assetAnchor := w.assetAnchor
  userAnchor := w.userAnchor
  timestamp := w.timestamp
  nonce := w.nonce
  blinding := w.blinding
  paddingSeed := w.paddingSeed
  optionalDummy := w.optionalDummy
  senderAddress := w.sender.address
  receiverAddress := w.receiver.address
  senderRnkDH := w.sender.rnkDH
  receiverRnkDH := w.receiver.rnkDH
  senderRnkCommitment := w.sender.rnkCommitment
  receiverRnkCommitment := w.receiver.rnkCommitment

theorem recovered_headers (w : TransferSem.Witness) :
    (recover w).anchor = w.anchor ∧ (recover w).assetAnchor = w.assetAnchor ∧
      (recover w).userAnchor = w.userAnchor ∧ (recover w).timestamp = w.timestamp ∧
      (recover w).nonce = w.nonce ∧ (recover w).blinding = w.blinding ∧
      (recover w).paddingSeed = w.paddingSeed ∧ (recover w).optionalDummy = w.optionalDummy :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem recovered_users (w : TransferSem.Witness) :
    (recover w).senderAddress = w.sender.address ∧
      (recover w).receiverAddress = w.receiver.address ∧
      (recover w).senderRnkDH = w.sender.rnkDH ∧
      (recover w).receiverRnkDH = w.receiver.rnkDH ∧
      (recover w).senderRnkCommitment = w.sender.rnkCommitment ∧
      (recover w).receiverRnkCommitment = w.receiver.rnkCommitment :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem recovered_inputs_legal (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) : Legal (recover w) := by
  rcases legal with ⟨canonical,
    ⟨_, sender, receiver, _, _, _, volume, _, _, balance⟩, _⟩
  simp only [CanonicalWitness, fieldsCanonical_append] at canonical
  rcases canonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header, _⟩, _⟩, _⟩, senderFields⟩, receiverFields⟩, _⟩, _⟩, _⟩
  refine ⟨header _ (by simp), header _ (by simp), header _ (by simp),
    volume.1, header _ (by simp), balance.1.2.2.2.2, header _ (by simp),
    sender.1.1, sender.2.2.1.1, receiver.1.1, receiver.2.2.1.1,
    sender.2.2.2.2.1.1, receiver.2.2.2.2.1.1, ?_, ?_⟩
  · exact senderFields _ (by simp [userFields])
  · exact receiverFields _ (by simp [userFields])

theorem recovered_seed_canonical (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) : CanonicalWitness (construct (recover w)) :=
  constructed_canonical (recover w) (recovered_inputs_legal c w legal)

theorem seed_anchor_identification (w : TransferSem.Witness) :
    w.assetAnchor = (construct (recover w)).assetAnchor ∧
      w.userAnchor = (construct (recover w)).userAnchor ∧
      w.anchor = (construct (recover w)).anchor ∧
      w.blinding = (construct (recover w)).blinding :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option pp.all true in
#check @recovered_headers
#print axioms recovered_headers
set_option pp.all true in
#check @recovered_users
#print axioms recovered_users
set_option pp.all true in
#check @recovered_inputs_legal
#print axioms recovered_inputs_legal
set_option pp.all true in
#check @recovered_seed_canonical
#print axioms recovered_seed_canonical
set_option pp.all true in
#check @seed_anchor_identification
#print axioms seed_anchor_identification

end ShielddSecurity.TransferInitialWitnessDecomposition
