import ShielddSecurity.TransferEpkAllScopes
import ShielddSecurity.RuntimeTransferSpendAuthGenerator
import ShielddSecurity.NativeTransferAdmission

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferEpkNativeGenerator

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J
    ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)}

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
    ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) model)
  (standard : NativeSpendAuthGenerator.StandardSpendAuth upstream)

private theorem two_nonzero (four : (4 : F) ≠ 0) : (2 : F) ≠ 0 := by
  intro zero
  apply four
  calc
    (4 : F) = (2 : F) + 2 := by ring
    _ = 0 := by rw [zero, zero, zero_add]

theorem native_multiply_canonical (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (n : Nat) (canonical : n < Scalar.order)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1) :
    NativeTransferAdmission.nativeMultiply codec writer
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
      NativeSpendAuthGenerator.literal (n : F) =
        model.coordinates (n • upstream.embed (upstream.promote upstream.spendAuthSubgroup)) := by
  rw [← NativeSpendAuthGenerator.generator_coordinates upstream standard]
  unfold NativeTransferAdmission.nativeMultiply
  rw [GroupByteCodec.native_reader_coordinates codec writer _ imaginary model
    nonSquare imaginarySquare (two_nonzero four)]
  rw [TransferReduction.decode_canonical_cast codec n
    (lt_trans canonical (by decide : Scalar.order < Scalar.modulus))]

/-- Every satisfying six-scope assignment yields canonical nonzero scalars
and the actual owned native multiply outputs. The fixed generator operand is
derived; no caller-supplied desired EPK or baseMeaning appears as a premise. -/
theorem sound (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (satisfied : Satisfies rho TransferEpkAllScopes.rows) :
    ∃ values : List Nat, values.length = 6 ∧
      (∀ n ∈ values, 0 < n ∧ n < Scalar.order) ∧
      values.map (fun n : Nat => (n : F)) = TransferEpkAllScopes.inputValues rho ∧
      TransferEpkAllScopes.nativePoints rho = values.map (fun n : Nat =>
        NativeTransferAdmission.nativeMultiply codec writer
          ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
          NativeSpendAuthGenerator.literal (n : F)) := by
  obtain ⟨values,count,bounds,inputs,points⟩ := TransferEpkAllScopes.sound model rho
    (upstream.embed (upstream.promote upstream.spendAuthSubgroup)) one four imaginary
    nonSquare imaginarySquare (RuntimeTransferSpendAuthGenerator.base_meaning upstream standard) satisfied
  refine ⟨values,count,bounds,inputs,?_⟩
  rw [points]
  apply List.map_congr_left
  intro n member
  exact (native_multiply_canonical upstream standard codec writer n (bounds n member).2
    four imaginary nonSquare imaginarySquare).symm

/-- Six legal scalar inputs construct all six EPK row scopes sequentially,
preserving their input columns and all earlier EPK rows. The existing audited
finite write/frame construction is reused, with owned generator/order joins. -/
theorem complete (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec)
    (rho : Nat → F) (n0 n1 n2 n3 n4 n5 : Nat)
    (positive0 : 0 < n0) (canonical0 : n0 < Scalar.order) (meaning0 : rho 4930 = (n0 : F))
    (positive1 : 0 < n1) (canonical1 : n1 < Scalar.order) (meaning1 : rho 6334 = (n1 : F))
    (positive2 : 0 < n2) (canonical2 : n2 < Scalar.order) (meaning2 : rho 11611 = (n2 : F))
    (positive3 : 0 < n3) (canonical3 : n3 < Scalar.order) (meaning3 : rho 13629 = (n3 : F))
    (positive4 : 0 < n4) (canonical4 : n4 < Scalar.order) (meaning4 : rho 14891 = (n4 : F))
    (positive5 : 0 < n5) (canonical5 : n5 < Scalar.order) (meaning5 : rho 16153 = (n5 : F))
    (one : rho 0 = 1) (linked : rho 200692 = rho 0) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1) :
    Satisfies (TransferEpkAllScopes.construct rho n0 n1 n2 n3 n4 n5) TransferEpkAllScopes.rows ∧
      (∀ column ∈ TransferEpkAllScopes.inputColumns,
        TransferEpkAllScopes.construct rho n0 n1 n2 n3 n4 n5 column = rho column) ∧
      TransferEpkAllScopes.nativePoints (TransferEpkAllScopes.construct rho n0 n1 n2 n3 n4 n5) =
        [n0,n1,n2,n3,n4,n5].map (fun n : Nat => NativeTransferAdmission.nativeMultiply codec writer
          ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
          NativeSpendAuthGenerator.literal (n : F)) := by
  have done := TransferEpkAllScopes.complete model rho n0 n1 n2 n3 n4 n5
    (upstream.embed (upstream.promote upstream.spendAuthSubgroup))
    (NativeSpendAuthGenerator.generator_order upstream standard)
    positive0 canonical0 meaning0 positive1 canonical1 meaning1 positive2 canonical2 meaning2
    positive3 canonical3 meaning3 positive4 canonical4 meaning4 positive5 canonical5 meaning5
    one linked four imaginary nonSquare imaginarySquare
    (RuntimeTransferSpendAuthGenerator.base_meaning upstream standard)
  refine ⟨done.1,done.2.1,?_⟩
  rw [done.2.2]
  simp only [List.map_cons,List.map_nil,
    native_multiply_canonical upstream standard codec writer n0 canonical0 four imaginary nonSquare imaginarySquare,
    native_multiply_canonical upstream standard codec writer n1 canonical1 four imaginary nonSquare imaginarySquare,
    native_multiply_canonical upstream standard codec writer n2 canonical2 four imaginary nonSquare imaginarySquare,
    native_multiply_canonical upstream standard codec writer n3 canonical3 four imaginary nonSquare imaginarySquare,
    native_multiply_canonical upstream standard codec writer n4 canonical4 four imaginary nonSquare imaginarySquare,
    native_multiply_canonical upstream standard codec writer n5 canonical5 four imaginary nonSquare imaginarySquare]

set_option pp.all true in
#check @native_multiply_canonical
#print axioms native_multiply_canonical
set_option pp.all true in
#check @sound
#print axioms sound
set_option pp.all true in
#check @complete
#print axioms complete

end ShielddSecurity.TransferEpkNativeGenerator
