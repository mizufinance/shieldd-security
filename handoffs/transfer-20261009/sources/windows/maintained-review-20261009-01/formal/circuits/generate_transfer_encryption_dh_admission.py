"""Discharge actual DH input-base/generator premises from owned admissions.

The source publisher supplies independently qualified first and role captures,
retains their row kernels, and regenerates the consumed key meaning. This
renderer gives no runtime or kernel credit on its own.
"""
from .generate_hash_round import _signature_audits, linear
from .transfer_balance_rows import canonical
from .transfer_encryption_dh_keys import infer_regulated_selectors
from .transfer_encryption_dh_selection import match_selection
from .transfer_relation import RelationError


def generate(first, checked):
    for value, expected in ((first, 0), (checked, None)):
        metadata = value.get('metadata', {})
        role = metadata.get('role')
        if (value.get('qualified') is not True or
                metadata.get('schema') != 'shieldd-transfer-encryption-dh-v1' or
                type(role) is not int or role not in range(5) or
                (expected is not None and role != expected)):
            raise RelationError('DH admission qualified first/actual role required')
    for key in ('relation_digest', 'domain_size', 'full_rows', 'constant_copy'):
        if first['metadata'].get(key) != checked['metadata'].get(key):
            raise RelationError('DH admission same ordinary relation identity required')
    infer_regulated_selectors(first)
    match_selection(checked)
    def actual(value, observed):
        if observed[0] == 'native':
            if type(observed[1]) is not int:
                raise RelationError('DH admission actual native value required')
            return canonical([(0, observed[1])])
        if observed[0] != 'source' or observed[1] not in value['derived']:
            raise RelationError('DH admission actual captured LC missing')
        terms = value['derived'][observed[1]]
        if terms != canonical(terms):
            raise RelationError('DH admission canonical captured LC required')
        return terms
    for key in ('detection_key', 'payload_key'):
        left = tuple(actual(first, v) for v in first['bindings'][key])
        right = tuple(actual(checked, v) for v in checked['bindings'][key])
        if left != right:
            raise RelationError('DH admission selected-key LC differs across roles')
    role = checked['metadata']['role']
    slot = 0 if role <= 1 else role-1
    loop = f'RuntimeTransferEncryptionDh{role}Loop'
    native = f'RuntimeTransferEncryptionDh{role}Native'
    flag = f'RuntimeTransferEncryptionDh{role}Flag'
    selection = f'RuntimeTransferEncryptionDh{role}Selection'
    meaning = 'RuntimeTransferEncryptionKeyMeaning'
    admission = 'RuntimeTransferEncryptionKeyAdmission'
    name = f'RuntimeTransferEncryptionDh{role}Admission'
    epk = f'TransferEpkScope{slot+2}Relation'
    base = tuple(actual(checked, v) for v in checked['points']['base'])
    text = f'''import ShielddSecurity.{native}
import ShielddSecurity.{admission}
import ShielddSecurity.RuntimeTransferSpendAuthGenerator
'''
    if role:
        text += f'import ShielddSecurity.{flag}\nimport ShielddSecurity.{selection}\n'
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 350000
set_option maxRecDepth 2048
variable {{F : Type}} [Field F] [DecidableEq F] [CharP F Scalar.modulus] [Fintype F]

theorem base_source_role (rho : Nat → F) :
    {loop}.base rho = (⟨eval rho {linear(base[0])}, eval rho {linear(base[1])}⟩ : Group.Point F) := rfl
'''
    extra = (f'    (flagSatisfied : Satisfies rho {flag}.rawRows)\n'
             f'    (selectionSatisfied : Satisfies rho {selection}.rawRows)\n') if role else ''
    chosen = f'if eval rho {flag}.flag = 1 then detection else payload' if role else 'detection'
    text += f'''theorem selected_base (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
{extra}    : {loop}.base rho = '''
    if not role:
        text += f'{meaning}.selectedDetection rho := rfl\n'
    else:
        text += f'''if eval rho {flag}.flag = 1 then
      {meaning}.selectedDetection rho else {meaning}.selectedPayload rho := by
  have interpolation : {loop}.base rho = EncryptionDhSelection.select
      (eval rho {flag}.flag) ({meaning}.selectedDetection rho) ({meaning}.selectedPayload rho) := by
    apply congrArg₂ Group.Point.mk
    · exact {selection}.axis0_interpolation rho one four selectionSatisfied
    · exact {selection}.axis1_interpolation rho one four selectionSatisfied
  rw [interpolation, EncryptionDhSelection.boolean_selection _ _ _
    ({flag}.flag_boolean rho one four flagSatisfied)]
'''
    text += '''private theorem coefficient :
    (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F) =
      (RuntimeTransferRnkLoop.coefficientD : F) := by
  simpa only [RuntimeTransferRnkLoop.coefficientD, Int.cast_ofNat] using
    (RuntimeNativeEncryptionInitializationCoefficients.d_value (F := F))

variable {Q Encoded E S R K Signing J : Type} [AddCommGroup J]
  {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J
    (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F)}

private def loopModel : Group.StandardCurveModel J (RuntimeTransferRnkLoop.coefficientD : F) where
  coordinates := model.coordinates
  onCurve := by intro point; rw [← coefficient]; exact model.onCurve point
  covers := by intro point valid; rw [← coefficient] at valid; exact model.covers point valid
  injective := model.injective
  identity := model.identity
  addition := by intro left right; rw [← coefficient]; exact model.addition left right

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
  (nonSquare : Group.NoUnitSquare (RuntimeNativeEncryptionInitializationCoefficients.coefficientD : F))
  (imaginarySquare : imaginary * imaginary = -1)
include hex fq arithmetic initial square codec api ops upstream points
  imaginary nonSquare imaginarySquare
'''
    premises = f'''    (standardOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (meaningSatisfied : Satisfies rho {meaning}.rows)
    (detectionSatisfied : Satisfies rho RuntimeTransferEncryptionDetectionInverse.rawRows)
    (payloadSatisfied : Satisfies rho RuntimeTransferEncryptionRegisteredPayloadGuard.rawRows)
{extra}'''
    keys_call = f'''{admission}.represented_selected_keys hex fq arithmetic initial square codec api
      ops upstream points imaginary nonSquare imaginarySquare standardOrder rho one four
      meaningSatisfied detectionSatisfied payloadSatisfied'''
    text += f'''theorem admitted_base
{premises}    : ∃ inputBase : J, model.coordinates inputBase = {loop}.base rho ∧
      Scalar.order • inputBase = 0 ∧ inputBase ≠ 0 := by
  obtain ⟨detection,payload,detectionRole,detectionOrder,detectionNonzero,
      payloadRole,payloadOrder,payloadNonzero⟩ :=
    {keys_call}
  refine ⟨({chosen}), ?_, ?_, ?_⟩
'''
    if role:
        text += f'''  · rw [selected_base rho one four flagSatisfied selectionSatisfied]
    by_cases active : eval rho {flag}.flag = 1
    · simpa only [active, if_true] using detectionRole
    · simpa only [active, if_false] using payloadRole
  · by_cases active : eval rho {flag}.flag = 1
    · simpa only [active, if_true] using detectionOrder
    · simpa only [active, if_false] using payloadOrder
  · by_cases active : eval rho {flag}.flag = 1
    · simpa only [active, if_true] using detectionNonzero
    · simpa only [active, if_false] using payloadNonzero
'''
    else:
        text += f'''  · rw [selected_base rho one four]; exact detectionRole
  · exact detectionOrder
  · exact detectionNonzero
'''
    extras_call = ' flagSatisfied selectionSatisfied' if role else ''
    text += f'''theorem native_admitted
    (writer : GroupByteCodec.BEWrite codec)
    (standard : NativeSpendAuthGenerator.StandardSpendAuth upstream)
    (standardPrime : Nat.Prime Scalar.order)
{premises}    (epkSatisfied : Satisfies rho {epk}.rows)
    (dhSatisfied : Satisfies rho {loop}.rawRows) :
    {loop}.output rho = EncryptionDhNative.multiply writer (RuntimeTransferRnkLoop.coefficientD : F)
      ({loop}.base rho) (eval rho RuntimeTransferEncryptionDh{role}Scalar.privateValue) ∧
    {loop}.output rho ≠ Group.identityPoint ∧
    ({loop}.output rho).x * (({loop}.output rho).x)⁻¹ = 1 := by
  obtain ⟨inputBase,baseCoordinates,baseOrder,baseNonzero⟩ := admitted_base
    hex fq arithmetic initial square codec api ops upstream points imaginary nonSquare imaginarySquare
    standardOrder rho one four meaningSatisfied detectionSatisfied payloadSatisfied{extras_call}
  let generator := upstream.embed (upstream.promote upstream.spendAuthSubgroup)
  have generatorMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) =
      (loopModel (model := model)).coordinates generator :=
    RuntimeTransferSpendAuthGenerator.base_meaning upstream standard
  have baseRole : {loop}.base rho = (loopModel (model := model)).coordinates inputBase :=
    baseCoordinates.symm
  have loopNonSquare : Group.NoUnitSquare (RuntimeTransferRnkLoop.coefficientD : F) := by
    rw [← coefficient]; exact nonSquare
  refine ⟨?_, ?_, ?_⟩
  · exact {native}.native_same_assignment rho one four codec writer (loopModel (model := model))
      generator inputBase imaginary loopNonSquare imaginarySquare generatorMeaning baseRole epkSatisfied dhSatisfied
  · exact {native}.native_output_nonzero rho one four codec (loopModel (model := model))
      generator inputBase imaginary loopNonSquare imaginarySquare generatorMeaning baseRole
      standardPrime baseOrder baseNonzero epkSatisfied dhSatisfied
  · exact {native}.native_output_inverse rho one four codec (loopModel (model := model))
      generator inputBase imaginary loopNonSquare imaginarySquare generatorMeaning baseRole
      standardPrime baseOrder baseNonzero epkSatisfied dhSatisfied
#print axioms base_source_role
#print axioms selected_base
#print axioms admitted_base
#print axioms native_admitted
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
