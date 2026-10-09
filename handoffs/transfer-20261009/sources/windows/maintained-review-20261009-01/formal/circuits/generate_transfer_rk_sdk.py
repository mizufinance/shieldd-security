"""Fresh SDK/public-key input assignment join for exact RK subgroup rows.

Input coordinates are constructed by the global pinned codec path, never
assumed to equal a desired circuit/native result. Actual subgroup observer
qualification and instantiation of all SDK/FFI contracts remain separate.
"""
from .generate_transfer_rk_subgroup import completion_plan, _audits
from .generate_hash_round import linear
from .transfer_relation import RelationError
from . import transfer_fixed_spend as fixed
from .transfer_ownership import source_index
from . import transfer_rk_point_add as point_add


def generate(data, accepted_roles, extracted):
    plan=completion_plan(data,accepted_roles,extracted);state=plan['state'];copy=state['metadata']['constant_copy']
    point_lcs=[state['derived'][h] for h in state['inputs'][:2]]
    if any(len(lc)!=1 or lc[0][1]!=1 for lc in point_lcs):
        raise RelationError('SDK RK coordinate input must be exact witness LC')
    x,y=(lc[0][0] for lc in point_lcs)
    protected=[c for c in plan['kept'] if c not in set(extracted['allocation']['witnesses'])|{x,y}]
    out=['''import ShielddSecurity.GroupNativeSdk
import ShielddSecurity.RuntimeTransferRkSubgroupCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferRkSdkCompletion
''',f'''-- Exact public RK witness columns: {x},{y}; same qualified subgroup row selection.
-- SDK/FFI functional contracts are explicit; this fresh candidate is not evidence.
def publicColumns : List Nat := [{x},{y}]
def protectedColumns : List Nat := {protected}
def publicValues {{F E S R K Q J : Type}} [Field F] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J (RuntimeTransferRkSubgroupCones.coefficientD : F)}}
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr (RuntimeTransferRkSubgroupCones.coefficientD : F) model)
    (point : S) (column : Nat) : F :=
  if column = {x} then (fq.integer (sdk.x point) : F)
  else if column = {y} then (fq.integer (sdk.y point) : F) else 0
def publicBase {{F E S R K Q J : Type}} [Field F] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J (RuntimeTransferRkSubgroupCones.coefficientD : F)}}
    (base : Nat → F)
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr (RuntimeTransferRkSubgroupCones.coefficientD : F) model)
    (point : S) := patchAssignment base (publicValues sdk point) publicColumns
theorem native_public_read {{F E S R K Q J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J (RuntimeTransferRkSubgroupCones.coefficientD : F)}}
    (codec : TransferReduction.CanonicalField F) (decoder : GroupByteCodec.BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr (RuntimeTransferRkSubgroupCones.coefficientD : F) model)
    (base : Nat → F) (point : S) :
    GroupNativeAuthorization.readPoint decoder (fq.bytes (sdk.x point)) (fq.bytes (sdk.y point)) =
      some (⟨eval (publicBase base sdk point) {linear(point_lcs[0])},
        eval (publicBase base sdk point) {linear(point_lcs[1])}⟩ : Group.Point F) := by
  rw [GroupNativeSdk.native_point_read codec decoder sdk point,sdk.coordinates]
  simp [publicBase,publicValues,publicColumns,patchAssignment,eval]
theorem protected_columns : ∀ column ∈ protectedColumns,
    column ∈ RuntimeTransferRkSubgroupCompletion.callerColumns ∧ column ∉ publicColumns := by
  have checked : protectedColumns.all (fun column => decide
    (column ∈ RuntimeTransferRkSubgroupCompletion.callerColumns ∧ column ∉ publicColumns)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
theorem actual_public_key_rows_complete {{F E S R K Q J : Type}} [Field F]
    [CharP F Scalar.modulus] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J (RuntimeTransferRkSubgroupCones.coefficientD : F)}}
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr (RuntimeTransferRkSubgroupCones.coefficientD : F) model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (RuntimeTransferRkSubgroupCones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (base : Nat → F) (key : K) (point : S)
    (admitted : GroupNativeSdk.admissionGate sdk (sdk.keyBytes key) = some point)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    let seed := publicBase base sdk point
    let completed := RuntimeTransferRkSubgroupCompletion.assignment seed codec writer
      (model.coordinates (sdk.embed (sdk.promote point)))
    Satisfies completed RuntimeTransferRkSubgroupCompletion.rawRows ∧
      (∀ column ∈ protectedColumns, completed column = base column) := by
  let seed := publicBase base sdk point
  have legal := GroupNativeSdk.admission sdk (sdk.keyBytes key) point admitted
  have zero : seed 0 = base 0 := patchAssignment_preserves base _ publicColumns 0 (by decide)
  have copy : seed {copy} = base {copy} := patchAssignment_preserves base _ publicColumns {copy} (by decide)
  have seedOne : seed 0 = 1 := zero.trans one
  have seedLink : seed {copy} = seed 0 := copy.trans (linked.trans zero.symm)
  have inputX : eval seed {linear(point_lcs[0])} = (model.coordinates (sdk.embed (sdk.promote point))).x := by
    rw [sdk.coordinates]
    simp [seed,publicBase,publicValues,publicColumns,patchAssignment,eval]
  have inputY : eval seed {linear(point_lcs[1])} = (model.coordinates (sdk.embed (sdk.promote point))).y := by
    rw [sdk.coordinates]
    simp [seed,publicBase,publicValues,publicColumns,patchAssignment,eval]
  have complete := RuntimeTransferRkSubgroupCompletion.actual_rows_complete codec writer model
    imaginary nonSquare imaginarySquare two seed (sdk.embed (sdk.promote point))
    legal.2.1 legal.2.2 seedOne seedLink inputX inputY
  refine ⟨complete.1,?_⟩
  intro column member
  have kept := protected_columns column member
  exact (complete.2 column kept.1).trans (patchAssignment_preserves base _ publicColumns column kept.2)
''']
    out.append(_audits('',('native_public_read','protected_columns','actual_public_key_rows_complete')))
    out.append('end ShielddSecurity.RuntimeTransferRkSdkCompletion\n')
    return ''.join(out)


def generate_randomized(data,accepted_roles,extracted):
    """Compose production randomization/readers with the same public RK seed.

    Both compressed key admissions are independent success conditions. Native
    scalar and point meanings follow from globally functional SDK/codec laws;
    no coordinate, randomization result or row-satisfaction premise is added.
    """
    plan=completion_plan(data,accepted_roles,extracted);copy=plan['state']['metadata']['constant_copy']
    namespace='ShielddSecurity.RuntimeTransferRkSdkCompletion'
    source=generate(data,accepted_roles,extracted).removesuffix('end '+namespace+'\n')
    source+=f'''theorem actual_randomized_public_rows_complete {{F E S R K Q J : Type}} [Field F]
    [CharP F Scalar.modulus] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J (RuntimeTransferRkSubgroupCones.coefficientD : F)}}
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (decoder : GroupByteCodec.BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr
      (RuntimeTransferRkSubgroupCones.coefficientD : F) model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (RuntimeTransferRkSubgroupCones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (base : Nat → F) (key : K) (scalar : R) (keyPoint randomizedPoint : S)
    (keyAdmission : GroupNativeSdk.admissionGate sdk (sdk.keyBytes key) = some keyPoint)
    (randomizedAdmission : GroupNativeSdk.admissionGate sdk
      (sdk.keyBytes (sdk.randomize key scalar)) = some randomizedPoint)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    GroupNativeSdk.readScalar fq fr decoder scalar = some (fr.integer scalar : F) ∧
      codec.decode (fr.integer scalar : F) = fr.integer scalar ∧
      GroupNativeAuthorization.readAuthorization decoder writer
        (RuntimeTransferRkSubgroupCones.coefficientD : F)
        (fq.bytes (sdk.x keyPoint)) (fq.bytes (sdk.y keyPoint))
        (fq.bytes (sdk.x sdk.generator)) (fq.bytes (sdk.y sdk.generator))
        (fr.integer scalar : F) = some (model.coordinates (sdk.embed (sdk.promote randomizedPoint))) ∧
      (let seed := publicBase base sdk randomizedPoint
       let completed := RuntimeTransferRkSubgroupCompletion.assignment seed codec writer
         (model.coordinates (sdk.embed (sdk.promote randomizedPoint)))
       Satisfies completed RuntimeTransferRkSubgroupCompletion.rawRows ∧
         (∀ column ∈ protectedColumns, completed column = base column)) := by
  have native := GroupNativeSdk.randomized_native_authorization codec writer decoder sdk
    imaginary nonSquare imaginarySquare two key scalar keyPoint randomizedPoint keyAdmission randomizedAdmission
  have canonical := GroupNativeSdk.scalar_canonical codec fq fr decoder scalar
  have rows := actual_public_key_rows_complete codec writer sdk imaginary nonSquare imaginarySquare two
    base (sdk.randomize key scalar) randomizedPoint randomizedAdmission one linked
  exact ⟨native.1,canonical.2,native.2,rows⟩
'''
    source+=_audits('',('actual_randomized_public_rows_complete',))+'end '+namespace+'\n'
    return source


def generate_owned(data,accepted_roles,extracted):
    """Use the defined Shieldd programs in the existing public-row constructor.

    The only native interfaces supplied are globally interpreted upstream
    operations. Owned reader/admission/generator bodies are constructed by the
    handwritten adapters, while actual allocation/row coverage comes from the
    same strict subgroup extraction used by the original generator.
    """
    plan=completion_plan(data,accepted_roles,extracted);copy=plan['state']['metadata']['constant_copy']
    namespace='ShielddSecurity.RuntimeTransferRkSdkCompletion'
    source=generate_randomized(data,accepted_roles,extracted).removesuffix('end '+namespace+'\n')
    source=source.replace('import ShielddSecurity.GroupNativeSdk\n',
        'import ShielddSecurity.GroupNativeSdk\nimport ShielddSecurity.ShielddNativeAuthorization\n',1)
    source+=f'''theorem actual_owned_randomized_public_rows_complete
    {{F E S R K Q Signing J Encoded Native : Type}} [Field F]
    [CharP F Scalar.modulus] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J (RuntimeTransferRkSubgroupCones.coefficientD : F)}}
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
      (RuntimeTransferRkSubgroupCones.coefficientD : F) model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (RuntimeTransferRkSubgroupCones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (base : Nat → F) (verification : K) (randomizer : R) (actionPoint randomizedPoint : S)
    (actionAdmission : ShielddNativeSdk.nonidentity upstream
      (upstream.keyBytes verification) = some actionPoint)
    (randomizedAdmission : ShielddNativeSdk.nonidentity upstream
      (upstream.keyBytes (ShielddNativeSdk.planRk upstream verification randomizer)) = some randomizedPoint)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    ShielddNativeSdk.scalar (fq := fq) (fr := fr) backend randomizer = some (fr.integer randomizer : F) ∧
      codec.decode (fr.integer randomizer : F) = fr.integer randomizer ∧
      ShielddNativeAuthorization.authorization backend upstream codec writer verification randomizer =
        ShielddNativeSdk.key backend upstream (ShielddNativeSdk.planRk upstream verification randomizer) ∧
      (let seed := publicBase base (ShielddNativeSdk.sdk upstream) randomizedPoint
       let completed := RuntimeTransferRkSubgroupCompletion.assignment seed codec writer
         (model.coordinates (upstream.embed (upstream.promote randomizedPoint)))
       Satisfies completed RuntimeTransferRkSubgroupCompletion.rawRows ∧
         (∀ column ∈ protectedColumns, completed column = base column)) := by
  have scalarRead := ShielddNativeSdk.scalar_read (fq := fq) (fr := fr) backend randomizer
  have canonical := GroupNativeSdk.scalar_canonical codec fq fr (ShielddScalarReader.decoder backend) randomizer
  have native := ShielddNativeAuthorization.production_authorization_agrees codec writer backend upstream
    imaginary nonSquare imaginarySquare two verification randomizer actionPoint randomizedPoint
    actionAdmission randomizedAdmission
  have rows := actual_public_key_rows_complete codec writer (ShielddNativeSdk.sdk upstream)
    imaginary nonSquare imaginarySquare two base
    (ShielddNativeSdk.planRk upstream verification randomizer) randomizedPoint randomizedAdmission one linked
  exact ⟨scalarRead,canonical.2,native,rows⟩
'''
    source+=_audits('',('actual_owned_randomized_public_rows_complete',))+'end '+namespace+'\n'
    return source


def generate_full_owned_inputs(captures,accepted_roles,extractions):
    """Construct owned scalar/AK inputs for the exact all126 fixed program.

    Every source input must be a distinct unit witness LC preserved by the
    replayed full-loop recipe. This companion does not consume or invent a
    subgroup observation, and keeps the fixed standard SPEND_AUTH parameter
    interpretation separate from Transfer witness inputs.
    """
    ownership=fixed.fixed_completion_join(captures,accepted_roles,extractions)
    randomizer=fixed.randomizer_completion_plan(captures[0],accepted_roles,extractions[0])
    try:
        spend=accepted_roles['metadata']['spend'];observed=accepted_roles['observed']
        refs=[*spend['ak'],spend['randomizer']]
        if len(refs)!=3:raise RelationError('owned fixed inputs require exactly two AK coordinates')
        columns=[]
        for ref in refs:
            if not isinstance(ref,dict) or set(ref)!={'source'}:
                raise RelationError('owned fixed input must be exact source reference')
            terms=observed[source_index(ref['source'])]
            if (not isinstance(terms,(list,tuple)) or len(terms)!=1 or
                not isinstance(terms[0],(list,tuple)) or len(terms[0])!=2 or
                type(terms[0][0]) is not int or type(terms[0][1]) is not int or terms[0][1]!=1):
                raise RelationError('owned fixed inputs require exact unit witness LCs')
            columns.append(terms[0][0])
    except (KeyError,TypeError,IndexError) as error:
        raise RelationError('owned fixed input metadata malformed') from error
    x,y,value=columns;copy=ownership['constant_copy'];start=randomizer['bit_start']
    external=sorted(set(ownership['kept'])-set(range(start,start+252)))
    if (len(set(columns))!=3 or set(columns)&{0,copy} or value!=randomizer['value'] or
        not set(columns)<=set(external)):
        raise RelationError('owned fixed input aliases or is not preserved by full constructor')
    protected=sorted(set(external)-set(columns))
    A='RuntimeTransferFixedSpend';C='RuntimeTransferFixedSpendCompletion'
    out=f'''import ShielddSecurity.ShielddNativeAuthorization
import ShielddSecurity.RuntimeTransferFixedSpendCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferOwnedFixedInputs
def inputColumns : List Nat := {columns}
def protectedColumns : List Nat := {protected}
def inputValues {{F E S R K Q Signing J : Type}} [Field F] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J ({A}.coefficientD : F)}}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({A}.coefficientD : F) model)
    (actionPoint : S) (randomizer : R) (column : Nat) : F :=
  if column = {x} then (fq.integer (ShielddNativeSdk.coordinateX upstream actionPoint) : F)
  else if column = {y} then (fq.integer (ShielddNativeSdk.coordinateY upstream actionPoint) : F)
  else if column = {value} then (fr.integer randomizer : F) else 0
def seed {{F E S R K Q Signing J : Type}} [Field F] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J ({A}.coefficientD : F)}}
    (base : Nat → F)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({A}.coefficientD : F) model)
    (actionPoint : S) (randomizer : R) :=
  patchAssignment base (inputValues upstream actionPoint randomizer) inputColumns
def actionKey {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨rho {x},rho {y}⟩
/-- A fixed named standard/source parameter contract, independent of every
Transfer key/randomizer and circuit assignment. Discharging the actual
SPEND_AUTH bytes and full-Jubjub embedding remains an explicit obligation. -/
structure StandardSpendAuth {{F E S R K Q Signing J : Type}} [Field F] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J ({A}.coefficientD : F)}}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({A}.coefficientD : F) model) : Prop where
  fixedParameterCoordinates : ({A}.generator : Group.Point F) =
    model.coordinates (upstream.embed (upstream.promote upstream.spendAuthSubgroup))
theorem owned_seed_reads {{F E S R K Q Signing J Encoded Native : Type}} [Field F]
    [CharP F Scalar.modulus] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J ({A}.coefficientD : F)}}
    (codec : TransferReduction.CanonicalField F)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({A}.coefficientD : F) model)
    (base : Nat → F) (verification : K) (actionPoint : S) (randomizer : R)
    (accepted : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) = some actionPoint) :
    ShielddNativeSdk.scalar (fq := fq) (fr := fr) backend randomizer =
        some (seed base upstream actionPoint randomizer {value}) ∧
      ShielddNativeSdk.key backend upstream verification =
        some (actionKey (seed base upstream actionPoint randomizer)) := by
  constructor
  · rw [ShielddNativeSdk.scalar_read (fq := fq) (fr := fr) backend randomizer]
    simp [seed,inputValues,inputColumns,patchAssignment]
  · simp only [ShielddNativeSdk.key,accepted]
    rw [ShielddNativeSdk.native_point_read codec backend upstream actionPoint,
      upstream.affineMeaning (upstream.promote actionPoint)]
    simp [actionKey,seed,inputValues,inputColumns,patchAssignment,
      ShielddNativeSdk.coordinateX,ShielddNativeSdk.coordinateY]
theorem owned_fixed_rows_complete {{F E S R K Q Signing J : Type}} [Field F]
    [CharP F Scalar.modulus] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J ({A}.coefficientD : F)}}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({A}.coefficientD : F) model)
    (base : Nat → F) (actionPoint : S) (randomizer : R)
    (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    let initial := seed base upstream actionPoint randomizer
    let completed := {C}.construct initial (fr.integer randomizer)
    Satisfies completed {A}.rawRows ∧
      Group.OnCurve ({A}.coefficientD : F) ({A}.contribution completed) ∧
      completed {value} = (fr.integer randomizer : F) ∧
      actionKey completed = actionKey initial ∧
      (∀ column ∈ protectedColumns, completed column = base column) := by
  dsimp only
  let initial := seed base upstream actionPoint randomizer
  have meaning : initial {value} = (fr.integer randomizer : F) := by
    simp [initial,seed,inputValues,inputColumns,patchAssignment]
  have zero : initial 0 = base 0 := patchAssignment_preserves base _ inputColumns 0 (by decide)
  have copy : initial {copy} = base {copy} := patchAssignment_preserves base _ inputColumns {copy} (by decide)
  have initialOne : initial 0 = 1 := zero.trans one
  have initialLink : initial {copy} = initial 0 := copy.trans (linked.trans zero.symm)
  have completed := {C}.actual_rows_complete initial (fr.integer randomizer) (fr.bounded randomizer)
    meaning initialOne four imaginary nonSquare imaginarySquare initialLink
  refine ⟨completed.1,completed.2.1,(completed.2.2 {value} (by decide)).trans meaning,?_,?_⟩
  · exact congrArg₂ Group.Point.mk (completed.2.2 {x} (by decide)) (completed.2.2 {y} (by decide))
  · have checked : protectedColumns.all (fun column => decide
        (column ∈ {C}.external ∧ column ∉ inputColumns)) = true := by decide
    intro column member
    have kept := of_decide_eq_true (List.all_eq_true.mp checked column member)
    exact (completed.2.2 column kept.1).trans (patchAssignment_preserves base _ inputColumns column kept.2)
theorem owned_fixed_native_complete {{F E S R K Q Signing J : Type}} [Field F]
    [CharP F Scalar.modulus] [AddCommGroup J]
    {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
    {{model : Group.StandardCurveModel J ({A}.coefficientD : F)}}
    (codec : TransferReduction.CanonicalField F)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({A}.coefficientD : F) model)
    (standard : StandardSpendAuth upstream)
    (base : Nat → F) (actionPoint : S) (randomizer : R)
    (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    let initial := seed base upstream actionPoint randomizer
    let completed := {C}.construct initial (fr.integer randomizer)
    binary ({A}.decodedBits completed) = fr.integer randomizer ∧
      {A}.contribution completed = model.coordinates
        (fr.integer randomizer • upstream.embed (upstream.promote upstream.spendAuthSubgroup)) := by
  dsimp only
  let initial := seed base upstream actionPoint randomizer
  let built := {C}.construct initial (fr.integer randomizer)
  have completed := owned_fixed_rows_complete upstream base actionPoint randomizer one four linked
    imaginary nonSquare imaginarySquare
  have preserved := {C}.actual_rows_complete initial (fr.integer randomizer) (fr.bounded randomizer)
    (by simp [initial,seed,inputValues,inputColumns,patchAssignment])
    (by simp [initial,seed,inputValues,inputColumns,patchAssignment,one]) four imaginary nonSquare imaginarySquare
    (by simpa [initial,seed,inputValues,inputColumns,patchAssignment] using linked)
  have oneBuilt : built 0 = 1 := (preserved.2.2 0 (by decide)).trans
    (by simp [initial,seed,inputValues,inputColumns,patchAssignment,one])
  have canonical := {A}.actual_fixed_canonical built oneBuilt four imaginary model nonSquare imaginarySquare
    (upstream.embed (upstream.promote upstream.spendAuthSubgroup)) standard.fixedParameterCoordinates completed.1
  have meaning : eval built RuntimeTransferRandomizer.privateValue = (fr.integer randomizer : F) := by
    simpa [RuntimeTransferRandomizer.privateValue,eval] using completed.2.2.1
  have integer := congrArg codec.decode (canonical.2.1.trans meaning)
  rw [TransferReduction.decode_canonical_cast codec _
    (lt_trans canonical.1 (by decide : Scalar.order < Scalar.modulus)),
    TransferReduction.decode_canonical_cast codec _
    (lt_trans (fr.bounded randomizer) (by decide : Scalar.order < Scalar.modulus))] at integer
  exact ⟨integer,by simpa only [integer] using canonical.2.2⟩
'''
    out+=_audits('',('owned_seed_reads','owned_fixed_rows_complete','owned_fixed_native_complete'))
    return out+'end ShielddSecurity.RuntimeTransferOwnedFixedInputs\n'


def generate_support(authorization_data, accepted_roles, addition_extraction,
                     subgroup_data, subgroup_extraction, *, high_start):
    """Small frame exclusions for actual earlier-row assignment preservation.

    The earlier fixed-row coverage is supplied by its separately proved full
    constructor. Only the bounded addition/subgroup writes and public/private
    patches are checked here; no full126 row list is scanned or asserted.
    """
    addition = point_add.completion_plan(authorization_data, accepted_roles, addition_extraction)
    subgroup = completion_plan(subgroup_data, accepted_roles, subgroup_extraction)
    state = subgroup['state'];copy = state['metadata']['constant_copy']
    if addition_extraction['identity'] != subgroup_extraction['identity']:
        raise RelationError('RK support requires identical actual ordinary relation identity')
    if type(high_start) is not int or not 0 < high_start < copy:
        raise RelationError('RK support high-start frame parameter')
    inverse = next(stage for stage in addition['stages'] if stage['kind'] == 'quotient')['quotient']
    high_writes = [column for column in addition['writes'] if column != inverse]
    if not high_writes or min(high_writes) < high_start:
        raise RelationError('RK support compiler writes precede protected high-start')
    fixed_frame = (inverse,min(high_writes))
    addition_frame = (inverse+1,max(high_writes)+1)
    witnesses = subgroup_extraction['allocation']['witnesses']
    public = []
    for handle in state['inputs'][:2]:
        terms = state['derived'][handle]
        if len(terms) != 1 or terms[0][1] != 1:
            raise RelationError('RK support public coordinate must be a unit witness LC')
        public.append(terms[0][0])
    def outside(frame,column):
        return not (column < frame[0] or high_start <= column < frame[1] or column == copy)
    if (not all(outside(fixed_frame,c) for c in addition['writes']) or
            not all(outside(addition_frame,c) for c in subgroup['writes']+witnesses+public)):
        raise RelationError('RK support write/patch aliases earlier allocation frame')
    raw_addition = point_add.selection(authorization_data,accepted_roles,addition_extraction)[2]
    if any(outside(addition_frame,c) for row in raw_addition.values() for terms in row for c,_ in terms):
        raise RelationError('RK support actual addition row escapes outgoing allocation frame')
    A='RuntimeTransferRkAdditionCompletion';M='RuntimeTransferRkSubgroupMaterialization'
    C='RuntimeTransferRkSubgroupCompletion';S='RuntimeTransferRkSdkCompletion'
    out=f'''import ShielddSecurity.GroupCircuitSupportPreservation
import ShielddSecurity.{A}
import ShielddSecurity.{S}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferRkSupport

def fixedFrame : GroupFixedCircuitBounds.Frame := ⟨{fixed_frame[0]},{fixed_frame[1]}⟩
def additionFrame : GroupFixedCircuitBounds.Frame := ⟨{addition_frame[0]},{addition_frame[1]}⟩
def outsideFrame (frame : GroupFixedCircuitBounds.Frame)
    (stages : List GroupCircuitCompletion.Step) : Bool :=
  stages.all (fun stage => stage.writes.all
    (fun column => decide (¬GroupFixedCircuitBounds.covers {high_start} {copy} frame column)))

private theorem checked_outside (frame : GroupFixedCircuitBounds.Frame)
    (stages : List GroupCircuitCompletion.Step) (checked : outsideFrame frame stages = true) :
    ∀ stage ∈ stages, ∀ column ∈ stage.writes,
      ¬GroupFixedCircuitBounds.covers {high_start} {copy} frame column := by
  intro stage member column written
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked stage member) column written)

theorem addition_outside : ∀ stage ∈ {A}.completionSteps, ∀ column ∈ stage.writes,
    ¬GroupFixedCircuitBounds.covers {high_start} {copy} fixedFrame column :=
  checked_outside fixedFrame {A}.completionSteps (by decide)

theorem subgroup_outside : ∀ stage ∈ {M}.steps, ∀ column ∈ stage.writes,
    ¬GroupFixedCircuitBounds.covers {high_start} {copy} additionFrame column :=
  checked_outside additionFrame {M}.steps (by decide)

theorem patches_outside : ∀ column ∈ {S}.publicColumns ++ {C}.witnessColumns,
    ¬GroupFixedCircuitBounds.covers {high_start} {copy} additionFrame column := by
  have checked : ({S}.publicColumns ++ {C}.witnessColumns).all (fun column =>
    decide (¬GroupFixedCircuitBounds.covers {high_start} {copy} additionFrame column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)

theorem addition_rows_covered : GroupFixedCircuitBounds.RowsCovered
    {high_start} {copy} additionFrame {A}.rawRows := by
  have checked : {A}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (GroupFixedCircuitBounds.covers {high_start} {copy} additionFrame term.1))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked row member) term present)

theorem addition_preserves_support {{F : Type}} [Field F] (base : Nat → F)
    (prior : List Row) (covered : GroupFixedCircuitBounds.RowsCovered {high_start} {copy} fixedFrame prior)
    (row : Row) (member : row ∈ prior) (term : Nat × Int) (present : term ∈ row.a ++ row.b) :
    GroupCircuitCompletion.run base {A}.completionSteps term.1 = base term.1 :=
  GroupCircuitSupportPreservation.covered_run_support base {A}.completionSteps
    {high_start} {copy} fixedFrame prior covered addition_outside row member term present

theorem subgroup_preserves_support {{F : Type}} [Field F] (base : Nat → F)
    (prior : List Row) (covered : GroupFixedCircuitBounds.RowsCovered {high_start} {copy} additionFrame prior)
    (row : Row) (member : row ∈ prior) (term : Nat × Int) (present : term ∈ row.a ++ row.b) :
    GroupCircuitCompletion.run base {M}.steps term.1 = base term.1 :=
  GroupCircuitSupportPreservation.covered_run_support base {M}.steps
    {high_start} {copy} additionFrame prior covered subgroup_outside row member term present
'''
    out += _audits('',('addition_outside','subgroup_outside','patches_outside','addition_rows_covered',
                      'addition_preserves_support','subgroup_preserves_support'))
    return out+'end ShielddSecurity.RuntimeTransferRkSupport\n'
