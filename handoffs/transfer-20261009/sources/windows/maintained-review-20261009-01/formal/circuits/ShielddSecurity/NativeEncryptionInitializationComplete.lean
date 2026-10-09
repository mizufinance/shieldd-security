import ShielddSecurity.RuntimeNativeEncryptionInitializationBridge
import ShielddSecurity.RuntimeNativeEncryptionFieldFacts

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEncryptionInitializationComplete

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus] [Fintype F]

theorem negative_euler (codec : TransferReduction.CanonicalField F) :
    (-5 : F) ^ (Fintype.card F / 2) = -1 := by
  have even : Fintype.card F / 2 % 2 = 0 := by
    rw [TransferReduction.codec_cardinality codec]
    decide
  rw [neg_pow, neg_one_pow_eq_pow_mod_two, even, pow_zero, one_mul]
  exact RuntimeNativeEncryptionFieldFacts.five_euler codec

/-- The owned rational-map denominator condition follows from the finite
constant5 certificate; it is not supplied by an initialization caller. -/
theorem denominator (codec : TransferReduction.CanonicalField F) :
    Group.NoUnitSquare (-5 : F) := by
  intro value equation
  have nonzero : value ≠ 0 := by
    intro zero
    simp only [zero, mul_zero] at equation
    exact zero_ne_one equation
  have square : IsSquare (-5 : F) := by
    refine ⟨value⁻¹, ?_⟩
    calc
      (-5 : F) = ((-5 : F) * value * value) * (value⁻¹ * value⁻¹) := by
        field_simp [nonzero] <;> ring
      _ = value⁻¹ * value⁻¹ := by rw [equation, one_mul]
  have odd := NativeEncryptionFieldArithmetic.odd_characteristic (F := F)
  have positive := (FiniteField.isSquare_iff odd
    (neg_ne_zero.mpr (NativeEncryptionFieldArithmetic.five_nonzero (F := F)))).mp square
  rw [negative_euler codec] at positive
  exact Ring.neg_one_ne_one_of_char_ne_two odd positive

theorem k_nonzero : (NativeAssetMap.coefficientK : F) ≠ 0 := by
  rw [RuntimeNativeEncryptionInitializationCoefficients.k_value]
  exact NativeEncryptionFixedArithmetic.cast_nonzero
    52435875175126190479447740508185965837690552500527637822603658699938581143549
    (by decide) (by decide)

theorem detection_nonzero (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) :
    (NativeEncryptionFixedKeys.fixedValue
      (d := RuntimeNativeEncryptionInitializationCoefficients.coefficientD) codec api 28).x ≠ 0 := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  exact RuntimeNativeEncryptionInitializationBridge.detection_nonzero codec api
    prerequisites.1 prerequisites.2.1 prerequisites.2.2

theorem payload_nonzero (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) :
    (NativeEncryptionFixedKeys.fixedValue
      (d := RuntimeNativeEncryptionInitializationCoefficients.coefficientD) codec api 29).x ≠ 0 := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  exact RuntimeNativeEncryptionInitializationBridge.payload_nonzero codec api
    prerequisites.1 prerequisites.2.1 prerequisites.2.2

theorem fixed_value_nonzero (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F)
    (domain : Nat) (allowed : domain = 28 ∨ domain = 29) :
    (NativeEncryptionFixedKeys.fixedValue
      (d := RuntimeNativeEncryptionInitializationCoefficients.coefficientD) codec api domain).x ≠ 0 := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  exact RuntimeNativeEncryptionInitializationBridge.fixed_value_nonzero codec api
    prerequisites.1 prerequisites.2.1 prerequisites.2.2 domain allowed

variable {Q Encoded E S R K Signing J : Type} [AddCommGroup J]
  {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J
    (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F)}

/-- The actual SDK fixed key is nonidentity under the explicit global primitive
and standard-curve contracts. Owned field/parameter/root-choice checks are
derived; no chosen point, root, branch or nonidentity is supplied. -/
theorem sdk_fixed_nonzero
    (hex : ShielddNativeParameterBytes.HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F)
    (ops : NativeAssetMap.Primitives fq api)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
      (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F) model)
    (points : NativeAssetMap.PointPrimitives fq upstream)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (domain : Nat) (allowed : domain = 28 ∨ domain = 29) :
    upstream.embed (upstream.promote
      (NativeEncryptionFixedKeys.fixedGenerator hex fq arithmetic initial square
        api ops upstream points domain)) ≠ 0 := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  exact RuntimeNativeEncryptionInitializationBridge.sdk_fixed_nonzero
    hex fq arithmetic initial square codec api ops upstream points
    imaginary nonSquare imaginarySquare k_nonzero (denominator codec)
    RuntimeNativeEncryptionInitializationCoefficients.edwards_equation
    prerequisites.1 prerequisites.2.1 prerequisites.2.2 domain allowed

set_option pp.all true in
#check @negative_euler
#print axioms negative_euler
set_option pp.all true in
#check @denominator
#print axioms denominator
set_option pp.all true in
#check @k_nonzero
#print axioms k_nonzero
set_option pp.all true in
#check @detection_nonzero
#print axioms detection_nonzero
set_option pp.all true in
#check @payload_nonzero
#print axioms payload_nonzero
set_option pp.all true in
#check @fixed_value_nonzero
#print axioms fixed_value_nonzero
set_option pp.all true in
#check @sdk_fixed_nonzero
#print axioms sdk_fixed_nonzero

end ShielddSecurity.NativeEncryptionInitializationComplete
