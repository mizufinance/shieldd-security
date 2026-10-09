import ShielddSecurity.TransferAuthorizationBranchCompletion

set_option maxHeartbeats 200000

/-! Inverse of the raw authorization constructor on independently legal semantic
records. This direction starts with AuthorizationSem to establish coverage of
the legal input domain; the forward constructor never assumes that conclusion.
These results do not construct or extract the pinned circuit assignment. -/
namespace ShielddSecurity.TransferAuthorizationDecomposition

open TransferCore TransferSem TransferAuthorizationBranchCompletion

def recover (w : TransferSem.Witness) : RawInputs :=
  ⟨w.auth.ak, w.auth.nk, w.auth.randomizer⟩

theorem scalar_recovered (c : Crypto) (w : TransferSem.Witness)
    (legal : AuthorizationScalarSem c w) :
    computedIVK c (recover w) = w.auth.ivk ∧
      incomingHash c (recover w) / scalarOrder = w.auth.quotient := by
  have equation := legal.2.2.2
  change incomingHash c (recover w) = w.auth.ivk + scalarOrder * w.auth.quotient at equation
  constructor
  · unfold computedIVK
    rw [equation, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt legal.1]
  · rw [equation, Nat.add_mul_div_left _ _ (by decide : 0 < scalarOrder),
      Nat.div_eq_of_lt legal.1, Nat.zero_add]

theorem authorization_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : AuthorizationSem c w) : constructAuth c (recover w) = w.auth := by
  rcases legal with ⟨_, _, _, _, scalar, _, _, _, _, _, _, rk⟩
  have recovered := scalar_recovered c w scalar
  have point : computedRK c (recover w) = w.auth.rk := rk.symm
  unfold constructAuth
  rw [recovered.1, recovered.2, point]
  cases w.auth
  rfl

private theorem provisional_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : AuthorizationSem c w) : provisional c w (recover w) = w := by
  unfold provisional
  rw [authorization_reconstructed c w legal]

theorem sender_commitment_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : AuthorizationSem c w) : senderCommitment c w (recover w) = w.sender.rnkCommitment := by
  have commitment := legal.2.2.2.2.2.2.2.1
  unfold senderCommitment
  rw [provisional_reconstructed c w legal]
  split
  · exact commitment ‹w.regulated = true›
  · rfl

theorem full_record_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : AuthorizationSem c w) : construct c w (recover w) = w := by
  unfold construct
  rw [provisional_reconstructed c w legal, sender_commitment_reconstructed c w legal]

theorem recovered_inputs_legal (c : Crypto) (w : TransferSem.Witness)
    (legal : AuthorizationSem c w) (nkCanonical : w.auth.nk < fieldModulus) :
    LegalInputs c w (recover w) := by
  rcases legal with ⟨ak, akNonidentity, asset, ringNonidentity, scalar, owner, dh,
    _, randomizer, _, rkNonidentity, rk⟩
  have recovered := scalar_recovered c w scalar
  have point : computedRK c (recover w) = w.auth.rk := rk.symm
  refine ⟨ak, akNonidentity, nkCanonical, randomizer, asset, ringNonidentity, ?_, ?_, ?_, ?_⟩
  · rw [recovered.1]
    exact scalar.2.1
  · rw [recovered.1]
    exact owner
  · rw [recovered.1]
    exact dh
  · rw [point]
    exact rkNonidentity

set_option pp.all true in
#check @scalar_recovered
#print axioms scalar_recovered
set_option pp.all true in
#check @authorization_reconstructed
#print axioms authorization_reconstructed
set_option pp.all true in
#check @sender_commitment_reconstructed
#print axioms sender_commitment_reconstructed
set_option pp.all true in
#check @full_record_reconstructed
#print axioms full_record_reconstructed
set_option pp.all true in
#check @recovered_inputs_legal
#print axioms recovered_inputs_legal

end ShielddSecurity.TransferAuthorizationDecomposition
