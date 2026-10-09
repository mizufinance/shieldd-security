"""Admit actual selected keys from owned fixed initialization and guard rows.

The caller must supply independently qualified first-role metadata, the actual
cofactor extraction, and the persisted payload guard certificate. Runtime and
kernel source publishers retain those prerequisites; synthetic tests confer no
caller or runtime qualification.
"""
from . import transfer_encryption_registered_guard as guard
from . import generate_transfer_encryption_dh_key_meaning as keys
from .transfer_encryption_dh_keys import infer_regulated_selectors
from .transfer_relation import RelationError
from .generate_hash_round import _signature_audits, signed

FIXED = (
    (17832230285398775523840151435063191920633280288053987250961356462684628833490,
     52236742954115892447572473178524297982305297140137344394933767595493156073169),
    (49822839976625491399435002605169580882773999909559575334089637637825427273330,
     29108985603249989484651727880329493522712908252517904247459350893053326313050))


def generate(checked, cofactors, payload_guard):
    # Recheck all source roles with the maintained selector/cofactor consumer.
    keys.generate(checked,cofactors)
    inferred = infer_regulated_selectors(checked)
    _,_,point,flag,_ = guard.recheck(checked,payload_guard)
    for key,expected in zip(('detection_key','payload_key'),FIXED):
        if inferred['selectors'][key]['fallback'] != tuple(('native',v) for v in expected):
            raise RelationError('key admission actual fallback differs from owned fixed initialization')
    selected = inferred['selectors']['payload_key']
    leaf = tuple(checked['derived'][h[1]] for h in selected['leaf'])
    regulated = checked['derived'][inferred['regulated_candidate'][1]]
    if point!=leaf or flag!=regulated:
        raise RelationError('key admission actual payload guard point/flag role mismatch')
    name = 'RuntimeTransferEncryptionKeyAdmission'
    meaning = 'RuntimeTransferEncryptionKeyMeaning'
    inverse = 'RuntimeTransferEncryptionDetectionInverse'
    payload = 'RuntimeTransferEncryptionRegisteredPayloadGuard'
    text = f'''import ShielddSecurity.NativeEncryptionFixedAdmission
import ShielddSecurity.{meaning}
import ShielddSecurity.{inverse}
import ShielddSecurity.{payload}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 350000
set_option maxRecDepth 2048
variable {{F : Type}} [Field F] [DecidableEq F] [CharP F Scalar.modulus] [Fintype F]
'''
    for label,(x,y) in zip(('Detection','Payload'),FIXED):
        text += f'''theorem native{label}_literal (rho : Nat → F) (one : rho 0 = 1) :
    {meaning}.native{label} rho = (⟨{x},{y}⟩ : Group.Point F) := by
  apply congrArg₂ Group.Point.mk
'''
        for value in (x,y):
            text += f'''  · have checked := NativeEncryptionInitializationSquares.polynomial_certificate (F := F)
      ({signed(value)} : Int) {value} (by decide)
    simpa only [{meaning}.native{label}, eval, one, Int.cast_ofNat, Int.cast_neg,
      one_mul, mul_one, add_zero] using checked
'''
    text += f'''theorem detection_inverse_role (rho : Nat → F) :
    {inverse}.point rho = {meaning}.selectedDetection rho := rfl
theorem payload_guard_role (rho : Nat → F) :
    {payload}.point rho = {meaning}.leafPayload rho := rfl
theorem regulated_guard_role : {payload}.flag = {meaning}.flag := by decide

private theorem coefficient : (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F) =
    (RuntimeTransferCofactorCones.coefficientD : F) := by
  simpa only [RuntimeTransferCofactorCones.coefficientD, Int.cast_ofNat] using
    (RuntimeNativeEncryptionInitializationCoefficients.d_value (F := F))

variable {{Q Encoded E S R K Signing J : Type}} [AddCommGroup J]
  {{fr : GroupNativeSdk.FrBytes R}}
  {{model : Group.StandardCurveModel J
    (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F)}}

/-- Parameter transport keeps precisely the original coordinate function. -/
private def rowModel (model : Group.StandardCurveModel J
    (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F)) :
    Group.StandardCurveModel J (RuntimeTransferCofactorCones.coefficientD : F) where
  coordinates := model.coordinates
  onCurve := by
    intro point
    rw [← coefficient]
    exact model.onCurve point
  covers := by
    intro point valid
    rw [← coefficient] at valid
    exact model.covers point valid
  injective := model.injective
  identity := model.identity
  addition := by
    intro left right
    rw [← coefficient]
    exact model.addition left right

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

theorem fallback_inputs (rho : Nat → F) (one : rho 0 = 1) :
    ∃ detection payload : J,
      model.coordinates detection = {meaning}.nativeDetection rho ∧
      Scalar.order • detection = 0 ∧ detection ≠ 0 ∧
      model.coordinates payload = {meaning}.nativePayload rho ∧
      Scalar.order • payload = 0 ∧ payload ≠ 0 := by
  obtain ⟨detection,payload,detectionRole,detectionOrder,detectionNonzero,
      payloadRole,payloadOrder,payloadNonzero⟩ :=
    NativeEncryptionFixedAdmission.represented_keys hex fq arithmetic initial square codec api
      ops upstream points imaginary nonSquare imaginarySquare
  rw [← nativeDetection_literal rho one] at detectionRole
  rw [← nativePayload_literal rho one] at payloadRole
  exact ⟨detection,payload,detectionRole,detectionOrder,detectionNonzero,
    payloadRole,payloadOrder,payloadNonzero⟩

theorem represented_selected_keys
    (standardOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (meaningSatisfied : Satisfies rho {meaning}.rows)
    (detectionSatisfied : Satisfies rho {inverse}.rawRows)
    (payloadSatisfied : Satisfies rho {payload}.rawRows) :
    ∃ detection payload : J,
      model.coordinates detection = {meaning}.selectedDetection rho ∧
      Scalar.order • detection = 0 ∧ detection ≠ 0 ∧
      model.coordinates payload = {meaning}.selectedPayload rho ∧
      Scalar.order • payload = 0 ∧ payload ≠ 0 := by
  obtain ⟨fallbackD,fallbackP,fallbackRoleD,fallbackOrderD,fallbackNonzeroD,
      fallbackRoleP,fallbackOrderP,fallbackNonzeroP⟩ :=
    fallback_inputs hex fq arithmetic initial square codec api ops upstream points
      imaginary nonSquare imaginarySquare rho one
  obtain ⟨leafD,leafP,selectedD,selectedP,leafRoleD,leafOrderD,leafRoleP,leafOrderP,
      selectedRoleD,selectedRoleP,coordinatesD,orderD,coordinatesP,orderP⟩ :=
    {meaning}.represented_keys (rowModel model) standardOrder rho one four
      fallbackD fallbackP fallbackRoleD fallbackRoleP fallbackOrderD fallbackOrderP meaningSatisfied
  have nonzeroD : selectedD ≠ 0 := by
    apply {inverse}.represented_nonidentity
      (RuntimeTransferCofactorCones.coefficientD : F) (rowModel model) selectedD rho one four
    · exact coordinatesD.trans (detection_inverse_role rho).symm
    · exact detectionSatisfied
  have nonzeroP : selectedP ≠ 0 := by
    by_cases active : eval rho {meaning}.flag = 1
    · rw [selectedRoleP, if_pos active]
      apply {payload}.represented_nonidentity
        (RuntimeTransferCofactorCones.coefficientD : F) (rowModel model) leafP rho one four
      · exact leafRoleP.trans (payload_guard_role rho).symm
      · exact payloadSatisfied
      · simpa only [regulated_guard_role] using active
    · rw [selectedRoleP, if_neg active]
      exact fallbackNonzeroP
  exact ⟨selectedD,selectedP,coordinatesD,orderD,nonzeroD,coordinatesP,orderP,nonzeroP⟩
'''
    exports = ['nativeDetection_literal','nativePayload_literal','detection_inverse_role',
        'payload_guard_role','regulated_guard_role','fallback_inputs','represented_selected_keys']
    text += ''.join('#print axioms '+n+'\n' for n in exports)
    return name,_signature_audits(text+f'end ShielddSecurity.{name}\n')
