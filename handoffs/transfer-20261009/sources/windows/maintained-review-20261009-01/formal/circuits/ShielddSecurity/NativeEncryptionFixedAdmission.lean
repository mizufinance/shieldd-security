import ShielddSecurity.RuntimeNativeEncryptionFixed28Literal
import ShielddSecurity.RuntimeNativeEncryptionFixed29Literal

set_option maxHeartbeats 200000

namespace ShielddSecurity.NativeEncryptionFixedAdmission

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus] [Fintype F]
variable {Q Encoded E S R K Signing J : Type} [AddCommGroup J]
  {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J
    (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F)}
variable (hex : ShielddNativeParameterBytes.HexCodec Encoded)
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

include hex fq arithmetic initial square codec api ops upstream points
  imaginary nonSquare imaginarySquare

/-- Owned initialization discharges every fixed-key-specific branch and
nonidentity condition. Only global primitive and standard-curve contracts
remain; a requested fallback's coordinates or order are never premises. -/
theorem represented_keys : ∃ detection payload : J,
    model.coordinates detection =
      (⟨17832230285398775523840151435063191920633280288053987250961356462684628833490,
        52236742954115892447572473178524297982305297140137344394933767595493156073169⟩ : Group.Point F) ∧
    Scalar.order • detection = 0 ∧ detection ≠ 0 ∧
    model.coordinates payload =
      (⟨49822839976625491399435002605169580882773999909559575334089637637825427273330,
        29108985603249989484651727880329493522712908252517904247459350893053326313050⟩ : Group.Point F) ∧
    Scalar.order • payload = 0 ∧ payload ≠ 0 := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  obtain ⟨detection,payload,detectionRole,detectionOrder,payloadRole,payloadOrder⟩ :=
    NativeEncryptionFixedKeys.represented_keys hex fq arithmetic initial square codec api
      ops upstream points imaginary nonSquare imaginarySquare
      NativeEncryptionInitializationComplete.k_nonzero
      (NativeEncryptionInitializationComplete.denominator codec)
      RuntimeNativeEncryptionInitializationCoefficients.edwards_equation
      prerequisites.1 prerequisites.2.1 prerequisites.2.2
  have detectionNonzero : detection ≠ 0 := by
    intro zero
    have nonzero := NativeEncryptionInitializationComplete.detection_nonzero codec api
    rw [← detectionRole, zero, model.identity] at nonzero
    exact nonzero rfl
  have payloadNonzero : payload ≠ 0 := by
    intro zero
    have nonzero := NativeEncryptionInitializationComplete.payload_nonzero codec api
    rw [← payloadRole, zero, model.identity] at nonzero
    exact nonzero rfl
  rw [RuntimeNativeEncryptionFixed28Literal.fixed_value codec api] at detectionRole
  rw [RuntimeNativeEncryptionFixed29Literal.fixed_value codec api] at payloadRole
  exact ⟨detection,payload,detectionRole,detectionOrder,detectionNonzero,
    payloadRole,payloadOrder,payloadNonzero⟩

/-- The actual circuit native-point reader uses the admitted byte/field
backend and the initialized SDK key; a literal coordinate read is derived. -/
theorem detection_native_point {ByteEncoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) ByteEncoded Native) :
    ShielddNativeSdk.nativePoint backend upstream
      (NativeEncryptionFixedKeys.fixedGenerator hex fq arithmetic initial square
        api ops upstream points 28) =
      some (⟨17832230285398775523840151435063191920633280288053987250961356462684628833490,
        52236742954115892447572473178524297982305297140137344394933767595493156073169⟩ : Group.Point F) := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  rw [NativeEncryptionFixedKeys.native_point hex fq arithmetic initial square codec api
    ops upstream points imaginary nonSquare imaginarySquare
    NativeEncryptionInitializationComplete.k_nonzero
    (NativeEncryptionInitializationComplete.denominator codec)
    RuntimeNativeEncryptionInitializationCoefficients.edwards_equation
    prerequisites.1 prerequisites.2.1 prerequisites.2.2 backend 28 (by decide)]
  rw [RuntimeNativeEncryptionFixed28Literal.fixed_value codec api]

theorem payload_native_point {ByteEncoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) ByteEncoded Native) :
    ShielddNativeSdk.nativePoint backend upstream
      (NativeEncryptionFixedKeys.fixedGenerator hex fq arithmetic initial square
        api ops upstream points 29) =
      some (⟨49822839976625491399435002605169580882773999909559575334089637637825427273330,
        29108985603249989484651727880329493522712908252517904247459350893053326313050⟩ : Group.Point F) := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  rw [NativeEncryptionFixedKeys.native_point hex fq arithmetic initial square codec api
    ops upstream points imaginary nonSquare imaginarySquare
    NativeEncryptionInitializationComplete.k_nonzero
    (NativeEncryptionInitializationComplete.denominator codec)
    RuntimeNativeEncryptionInitializationCoefficients.edwards_equation
    prerequisites.1 prerequisites.2.1 prerequisites.2.2 backend 29 (by decide)]
  rw [RuntimeNativeEncryptionFixed29Literal.fixed_value codec api]

set_option pp.all true in
#check @represented_keys
#print axioms represented_keys
set_option pp.all true in
#check @detection_native_point
#print axioms detection_native_point
set_option pp.all true in
#check @payload_native_point
#print axioms payload_native_point

end ShielddSecurity.NativeEncryptionFixedAdmission
