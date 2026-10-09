import ShielddSecurity.TransferAssetMapSdkRelation
import ShielddSecurity.TransferBalanceGroupRelation

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceOwnedAssetRelation

def rows : List Row := TransferAssetMapArbitraryNative.rows ++ TransferBalanceGroupRelation.rows

variable {F E S R K Q Signing J Encoded : Type}
variable [Field F] [CharP F Scalar.modulus] [DecidableEq F] [Fintype F] [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr (RuntimeJubjub.d : F) model)
variable (codec : TransferReduction.CanonicalField F)
variable (hex : ShielddNativeParameterBytes.HexCodec Encoded)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (api : ElligatorNativeRoots.SqrtAPI F)
variable (ops : NativeAssetMap.Primitives fq api)
variable (points : NativeAssetMap.PointPrimitives fq upstream)

include codec

/-- The captured asset hash/map rows discharge the balance loop's asset-point
meaning. Native amount/asset input and fixed blinding-base source joins remain
explicit; the signed difference and final commitment are derived from rows. -/
theorem sound (cardinality : Fintype.card F = Scalar.modulus)
    (rho : Nat → F) (asset : Q) (assetInput : rho 6 = (fq.integer asset : F))
    (one : rho 0 = 1) (linked : rho 200692 = rho 0) (four : (4 : F) ≠ 0)
    (blindingBase : J)
    (blindingMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) = model.coordinates blindingBase)
    (amounts : TransferSignedMagnitude.Inputs)
    (amountMeanings : ∀ i,rho (RuntimeTransferSignedBalanceCompletion.amountColumns i) = ((amounts i).val : F))
    (satisfied : Satisfies rho rows) :
    ∃ b : Nat,b < Scalar.order ∧ (b : F) = rho 2 ∧
      RuntimeTransferBalanceFinalAddCompletion.outputPoint rho = model.coordinates
        (((TransferSignedMagnitude.inputTotal amounts : Int) -
          (TransferSignedMagnitude.outputTotal amounts : Int)) •
          (upstream.embed (upstream.promote
            (NativeAssetGeneratorSource.valueGenerator hex fq arithmetic initial square api ops upstream points asset))) +
          b • blindingBase) := by
  have mapRows : Satisfies rho TransferAssetMapArbitraryNative.rows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have balanceRows : Satisfies rho TransferBalanceGroupRelation.rows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  have assetMeaning := TransferAssetMapSdkRelation.balance_input fq fr model upstream codec hex arithmetic initial
    square api ops points cardinality rho asset assetInput one four mapRows
  exact TransferBalanceGroupRelation.sound rho one linked four RuntimeJubjub.imaginary
    (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square model _ blindingBase assetMeaning
    blindingMeaning amounts amountMeanings balanceRows

set_option pp.all true in
#check @sound
#print axioms sound

end ShielddSecurity.TransferBalanceOwnedAssetRelation
