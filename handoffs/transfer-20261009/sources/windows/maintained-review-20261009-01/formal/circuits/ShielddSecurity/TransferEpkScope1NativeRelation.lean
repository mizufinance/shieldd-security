import ShielddSecurity.TransferEpkScope1Relation
import ShielddSecurity.NativeEphemeralSdk

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEpkScope1NativeRelation

variable {F : Type} [Field F] [CharP F Scalar.modulus]

theorem scalar_value (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (n : Nat) (bounded : n < Scalar.order) (meaning : (n : F) = rho 6334) :
    codec.decode (rho 6334) = n := by
  rw [← meaning]
  exact TransferReduction.decode_canonical_cast codec n
    (bounded.trans (by decide : Scalar.order < Scalar.modulus))

theorem sdk_epk {E S R K Q J : Type} [AddCommGroup J]
    {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
    (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (decoder : GroupByteCodec.BERead (F := F))
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) model)
    (rho : Nat → F) (esk : R) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (two : (2 : F) ≠ 0)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) =
      model.coordinates (sdk.embed sdk.spendAuth))
    (scalarMeaning : rho 6334 = (fr.integer esk : F))
    (satisfied : Satisfies rho TransferEpkScope1Relation.rows) :
    0 < fr.integer esk ∧ NativeEphemeralSdk.readEphemeral codec writer decoder sdk esk =
      some (⟨rho 6326,rho 6327⟩ : Group.Point F) := by
  have derived := TransferEpkScope1Relation.sound model rho (sdk.embed sdk.spendAuth)
    one four imaginary nonSquare imaginarySquare baseMeaning satisfied
  have decoded : codec.decode (rho 6334) = TransferEpkScope1Relation.scalar rho :=
    scalar_value codec rho _ derived.2.1 derived.2.2.1
  have nativeDecoded : codec.decode (rho 6334) = fr.integer esk := by
    rw [scalarMeaning]
    exact TransferReduction.decode_canonical_cast codec (fr.integer esk)
      ((fr.bounded esk).trans (by decide : Scalar.order < Scalar.modulus))
  have same : TransferEpkScope1Relation.scalar rho = fr.integer esk := decoded.symm.trans nativeDecoded
  constructor
  · simpa only [same] using derived.1
  · rw [NativeEphemeralSdk.native_epk_coordinates codec writer decoder sdk imaginary
      nonSquare imaginarySquare two]
    apply congrArg some
    have point : (⟨rho 6326,rho 6327⟩ : Group.Point F) =
        model.coordinates (fr.integer esk • sdk.embed sdk.spendAuth) := by
      simpa only [same] using derived.2.2.2
    exact point.symm

set_option pp.all true in
#check @scalar_value
#print axioms scalar_value
set_option pp.all true in
#check @sdk_epk
#print axioms sdk_epk

end ShielddSecurity.TransferEpkScope1NativeRelation
