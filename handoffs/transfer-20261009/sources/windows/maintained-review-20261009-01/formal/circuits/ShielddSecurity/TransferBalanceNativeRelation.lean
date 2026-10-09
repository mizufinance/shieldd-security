import ShielddSecurity.TransferBalanceGroupRelation
import ShielddSecurity.NativeBalanceCommitment

set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferBalanceNativeRelation

def inputs (amounts : TransferSignedMagnitude.Inputs) : NativeTransferAdmission.Amounts :=
  ⟨amounts 0, amounts 1⟩

def outputs (amounts : TransferSignedMagnitude.Inputs) : NativeTransferAdmission.Amounts :=
  ⟨amounts 2, amounts 3⟩

theorem net_value (amounts : TransferSignedMagnitude.Inputs) (net : NativeBalanceCommitment.Net)
    (success : NativeBalanceCommitment.sdkNet (inputs amounts) (outputs amounts) = some net) :
    NativeBalanceCommitment.signedValue net =
      (TransferSignedMagnitude.inputTotal amounts : Int) -
      (TransferSignedMagnitude.outputTotal amounts : Int) := by
  have exactNet := (NativeBalanceCommitment.sdk_net_success _ _ net success).2.2
  rw [exactNet, NativeBalanceCommitment.canonical_net_value]
  rfl

theorem blinding_value {F : Type} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (b : Nat)
    (bounded : b < Scalar.order) (meaning : (b : F) = rho 2) :
    codec.decode (rho 2) = b := by
  rw [← meaning]
  exact TransferReduction.decode_canonical_cast codec b
    (bounded.trans (by decide : Scalar.order < Scalar.modulus))

/-- The circuit's existential blinding is identified with the canonical native
codec, and the integer net comes from the successful SDK fold. Source agreement
of codecs, amounts and both generator meanings remains explicit. -/
theorem sdk_commitment {F J : Type} [Field F] [AddCommGroup J] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferBalanceFinalAddCompletion.d : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (model : Group.StandardCurveModel J (RuntimeTransferBalanceFinalAddCompletion.d : F))
    (asset blindingBase : J)
    (assetMeaning : RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho = model.coordinates asset)
    (blindingMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) = model.coordinates blindingBase)
    (amounts : TransferSignedMagnitude.Inputs)
    (amountMeanings : ∀ i, rho (RuntimeTransferSignedBalanceCompletion.amountColumns i) = ((amounts i).val : F))
    (net : NativeBalanceCommitment.Net)
    (success : NativeBalanceCommitment.sdkNet (inputs amounts) (outputs amounts) = some net)
    (satisfied : Satisfies rho TransferBalanceGroupRelation.rows) :
    RuntimeTransferBalanceFinalAddCompletion.outputPoint rho = model.coordinates
      (NativeBalanceCommitment.sdkCommitment asset blindingBase net (codec.decode (rho 2))) := by
  obtain ⟨b, bounded, meaning, result⟩ := TransferBalanceGroupRelation.sound rho one linked
    four imaginary nonSquare imaginarySquare model asset blindingBase assetMeaning
    blindingMeaning amounts amountMeanings satisfied
  have decoded := blinding_value codec rho b bounded meaning
  unfold NativeBalanceCommitment.sdkCommitment
  rw [net_value amounts net success, decoded]
  exact result

set_option pp.all true in
#check @net_value
#print axioms net_value
set_option pp.all true in
#check @blinding_value
#print axioms blinding_value
set_option pp.all true in
#check @sdk_commitment
#print axioms sdk_commitment
end ShielddSecurity.TransferBalanceNativeRelation
