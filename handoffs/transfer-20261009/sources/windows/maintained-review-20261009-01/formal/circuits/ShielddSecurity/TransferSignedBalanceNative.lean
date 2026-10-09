import ShielddSecurity.TransferSignedMagnitude
import ShielddSecurity.NativeBalanceCommitment

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.TransferSignedBalanceNative

abbrev inputPair (amounts : TransferSignedMagnitude.Inputs) : NativeTransferAdmission.Amounts :=
  (amounts 0,amounts 1)
abbrev outputPair (amounts : TransferSignedMagnitude.Inputs) : NativeTransferAdmission.Amounts :=
  (amounts 2,amounts 3)

/-- These are the actual constructor's four amounts and its computed sign;
no signed-net equation or desired group point is supplied by the caller. -/
theorem signed_difference (amounts : TransferSignedMagnitude.Inputs) :
    (if TransferSignedMagnitude.negative amounts then
      -(TransferSignedMagnitude.magnitude amounts : Int) else
      (TransferSignedMagnitude.magnitude amounts : Int)) =
    (TransferSignedMagnitude.inputTotal amounts : Int) -
      (TransferSignedMagnitude.outputTotal amounts : Int) := by
  by_cases less : TransferSignedMagnitude.inputTotal amounts < TransferSignedMagnitude.outputTotal amounts
  · simp only [TransferSignedMagnitude.negative,TransferSignedMagnitude.magnitude,
      less,decide_true,if_true]
    omega
  · simp only [TransferSignedMagnitude.negative,TransferSignedMagnitude.magnitude,
      less,decide_false,Bool.false_eq_true,if_false]
    omega

theorem sdk_net_signed_value (amounts : TransferSignedMagnitude.Inputs)
    (net : NativeBalanceCommitment.Net)
    (success : NativeBalanceCommitment.sdkNet (inputPair amounts) (outputPair amounts) = some net) :
    NativeBalanceCommitment.signedValue net =
      if TransferSignedMagnitude.negative amounts then
        -(TransferSignedMagnitude.magnitude amounts : Int) else
        (TransferSignedMagnitude.magnitude amounts : Int) := by
  have observed := NativeBalanceCommitment.sdk_net_success (inputPair amounts) (outputPair amounts) net success
  calc
    _ = (TransferSignedMagnitude.inputTotal amounts : Int) -
        (TransferSignedMagnitude.outputTotal amounts : Int) := by
      rw [observed.2.2,NativeBalanceCommitment.canonical_net_value]
      rfl
    _ = _ := (signed_difference amounts).symm

/-- Native statement success and successful SDK folds are independent source
preconditions. Their coordinates agree with the computed signed magnitude.
The actual variable/fixed multiplication row transport remains separate. -/
theorem native_signed_commitment {F J : Type} [Field F] [DecidableEq F]
    [CharP F Scalar.modulus] [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (two : (2 : F) ≠ 0) (base blindingBase : J) (asset : F)
    (amounts : TransferSignedMagnitude.Inputs) (blinding : F) (net : NativeBalanceCommitment.Net)
    (sdkSuccess : NativeBalanceCommitment.sdkNet (inputPair amounts) (outputPair amounts) = some net)
    (value : Group.Point F)
    (nativeSuccess : NativeTransferAdmission.balanceNative codec writer d
      (fun _ => model.coordinates base) (model.coordinates blindingBase)
      asset (inputPair amounts) (outputPair amounts) blinding = .ok value) :
    value = model.coordinates
      ((if TransferSignedMagnitude.negative amounts then
          -(TransferSignedMagnitude.magnitude amounts : Int) else
          (TransferSignedMagnitude.magnitude amounts : Int)) • base +
        codec.decode blinding • blindingBase) := by
  have observed := NativeBalanceCommitment.native_balance_commitment codec writer d imaginary model
    nonSquare imaginarySquare two base blindingBase asset (inputPair amounts) (outputPair amounts)
    blinding net sdkSuccess value nativeSuccess
  unfold NativeBalanceCommitment.sdkCommitment at observed
  rw [sdk_net_signed_value amounts net sdkSuccess] at observed
  exact observed

set_option pp.all true in
#check @signed_difference
#print axioms signed_difference
set_option pp.all true in
#check @sdk_net_signed_value
#print axioms sdk_net_signed_value
set_option pp.all true in
#check @native_signed_commitment
#print axioms native_signed_commitment

end ShielddSecurity.TransferSignedBalanceNative
