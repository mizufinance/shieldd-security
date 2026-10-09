import ShielddSecurity.TransferReduction

set_option maxHeartbeats 150000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeAssetAdmission

inductive Error where
  | reservedZero
  | registryFailure
  deriving DecidableEq

variable {F : Type} [Field F] [DecidableEq F]

/-- Pinned ComplianceRegistryRead::get_asset_proof_data rejects asset zero
before the regulation lookup and either membership/gap branch. The callback
retains the registry operations and their failures; it asserts no row truth,
authenticated root, or desired generated value. Arbitrary caller-supplied
ActionWitness::validate success is a distinct interface. -/
def proofDataNative {Proof : Type} (fetch : F → Except Error Proof)
    (asset : F) : Except Error Proof :=
  if asset = 0 then .error .reservedZero else fetch asset

theorem proof_data_success_nonzero {Proof : Type} (fetch : F → Except Error Proof)
    (asset : F) (proof : Proof)
    (accepted : proofDataNative fetch asset = .ok proof) : asset ≠ 0 := by
  intro zero
  simp only [proofDataNative,zero,if_true] at accepted
  cases accepted

theorem proof_data_zero_rejected {Proof : Type} (fetch : F → Except Error Proof) :
    proofDataNative fetch 0 = .error .reservedZero := by
  simp only [proofDataNative,if_true]

theorem proof_data_success_fetch {Proof : Type} (fetch : F → Except Error Proof)
    (asset : F) (proof : Proof)
    (accepted : proofDataNative fetch asset = .ok proof) : fetch asset = .ok proof := by
  have nonzero := proof_data_success_nonzero fetch asset proof accepted
  simpa only [proofDataNative,if_neg nonzero] using accepted

/-- The native unregulated witness branch compares canonical bytes strictly
against its predecessor. The canonical codec interprets that unsigned order;
the independent byte-order/source correspondence remains explicit. No field
reconstruction capacity premise is used. -/
theorem unregulated_gap_nonzero [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (predecessor asset : F)
    (gap : codec.decode predecessor < codec.decode asset) : asset ≠ 0 := by
  intro zero
  have decodedZero : codec.decode (0 : F) = 0 := by
    simpa only [Nat.cast_zero] using
      TransferReduction.decode_canonical_cast codec 0 (by decide)
  rw [zero,decodedZero] at gap
  exact Nat.not_lt_zero _ gap

set_option pp.all true in
#check @proof_data_success_nonzero
#print axioms proof_data_success_nonzero
set_option pp.all true in
#check @proof_data_zero_rejected
#print axioms proof_data_zero_rejected
set_option pp.all true in
#check @proof_data_success_fetch
#print axioms proof_data_success_fetch
set_option pp.all true in
#check @unregulated_gap_nonzero
#print axioms unregulated_gap_nonzero

end ShielddSecurity.NativeAssetAdmission
