"""Bounded support and owned authorization composition candidates.

Imported maintained modules must already have an exact runtime extraction and
dependency inventory. These source checks select their declared row lists;
kernel support checks inspect those imported expressions. Neither source
matching nor dependency hashes qualify a runtime observation.
"""
import hashlib
import re
from .transfer_relation import RelationError

FIXED_STARTS=tuple(range(0,126,16))


def _body(module,data):
    if not isinstance(data,bytes) or len(data)>2**20:
        raise RelationError('bounded maintained authorization module source')
    try:text=data.decode('utf8')
    except UnicodeError as error:raise RelationError('authorization module encoding') from error
    text=text.replace('\r\n','\n')
    starts=re.findall(r'^namespace ShielddSecurity\.([A-Za-z0-9_]+)\s*$',text,re.MULTILINE)
    start='namespace ShielddSecurity.'+module+'\n';end='end ShielddSecurity.'+module
    if starts.count(module)!=1 or text.count(end+'\n')!=1 or not text.rstrip().endswith(end):
        raise RelationError('one exact maintained main namespace')
    if text.count(start)!=1:raise RelationError('maintained main namespace line')
    return text.split(start,1)[1].rsplit(end,1)[0]


def _declared_blocks(module,data,declaration,blocks,raw_declaration):
    body=_body(module,data)
    match=re.findall(r'^def '+declaration+r' : List \(List Row\) := \[([^\n]*)\]\s*$',body,re.MULTILINE)
    if len(match)!=1 or re.sub(r'\s+','',match[0])!=','.join(blocks):
        raise RelationError('exact ordered maintained row blocks')
    if body.count('def '+raw_declaration+' : List Row := '+declaration+'.flatten')!=1:
        raise RelationError('exact maintained flattened rows')


def _coverage(module,data,blocks,declaration='blocks',raw_declaration='rawRows',proofs=None):
    name=module+'_Frame'
    source=f'''import ShielddSecurity.CompilerFrameCoverage
import ShielddSecurity.{module}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Maintained dependency SHA256: {hashlib.sha256(data).hexdigest()}
-- Finite support only; imported constructor and runtime replay scopes separate.
def frame : GroupFixedCircuitBounds.Frame := ⟨4271,64440⟩
'''
    for index,block in enumerate(blocks):
        if proofs is None:
            source+=f'''private theorem block{index:02d} : GroupFixedCircuitBounds.RowsCovered 22738 200692 frame {block} :=
  CompilerFrameCoverage.checked_rows 22738 200692 frame _ (by decide)
'''
        else:
            source+=f'''private theorem block{index:02d} : GroupFixedCircuitBounds.RowsCovered 22738 200692 frame {block} :=
  {proofs[index]}
'''
    source+=f'''theorem rows_covered : GroupFixedCircuitBounds.RowsCovered 22738 200692 frame {module}.{raw_declaration} := by
  intro row member term present
  obtain ⟨block,blockMember,rowMember⟩ := List.mem_flatten.mp member
  simp only [{module}.{declaration},List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at blockMember
  rcases blockMember with '''+' | '.join('rfl' for _ in blocks)+'\n'
    source+=''.join(f'  · exact block{index:02d} row rowMember term present\n' for index in range(len(blocks)))
    source+='''set_option pp.all true in
#check @rows_covered
#print axioms rows_covered
'''+f'end ShielddSecurity.{name}\n'
    return name,source


def generate_fixed_coverage(sources):
    """Ten candidates: eight ≤16-window checks, comparator blocks, symbolic join.

    This only checks columns appearing in real imported row expressions. The
    final join inspects nine block names and never walks all126 sparse rows.
    Randomizer checks use the original comparator rows, including constant
    copy and reconstruction tail, rather than a shortened semantic template.
    """
    chunks=[f'RuntimeFixedSpendChunk{start:03d}' for start in FIXED_STARTS]
    windows=[f'RuntimeFixedSpendWindow{index:03d}' for index in range(126)]
    expected=set(chunks+windows+['RuntimeTransferRandomizer','RuntimeTransferFixedSpend'])
    if not isinstance(sources,dict) or set(sources)!=expected:
        raise RelationError('exact all126 fixed support dependency inventory')
    modules={}
    for start,module in zip(FIXED_STARTS,chunks):
        blocks=['ShielddSecurity.'+windows[index]+'.rawRows' for index in range(start,min(start+16,126))]
        for index in range(start,min(start+16,126)):
            body=_body(windows[index],sources[windows[index]])
            if body.count('def rawRows : List Row :=')!=1:
                raise RelationError('one actual window original row declaration')
        _declared_blocks(module,sources[module],'blocks',blocks,'rawRows')
        name,source=_coverage(module,sources[module],blocks)
        modules[name]=source
    randomizer='RuntimeTransferRandomizer'
    short=[f'c{index}Raw' for index in range(16)]+['tailRaw']
    body=_body(randomizer,sources[randomizer])
    if any(body.count('def '+block+' : List Row :=')!=1 for block in short):
        raise RelationError('all16 original comparator chunks and tail')
    _declared_blocks(randomizer,sources[randomizer],'originalBlocks',short,'originalRows')
    name,source=_coverage(randomizer,sources[randomizer],[randomizer+'.'+block for block in short],
        'originalBlocks','originalRows')
    modules[name]=source
    whole='RuntimeTransferFixedSpend'
    blocks=['ShielddSecurity.'+chunk+'.rawRows' for chunk in chunks]+[
        'ShielddSecurity.'+randomizer+'.originalRows']
    _declared_blocks(whole,sources[whole],'blocks',blocks,'rawRows')
    proofs=[chunk+'_Frame.rows_covered' for chunk in chunks]+[randomizer+'_Frame.rows_covered']
    name,source=_coverage(whole,sources[whole],blocks,proofs=proofs)
    imports=''.join('import ShielddSecurity.'+proof.split('.')[0]+'\n' for proof in proofs)
    modules[name]=imports+source
    return modules


def generate_owned_join(captures,accepted_roles,extractions,authorization_data,addition_extraction,
                        subgroup_data,subgroup_extraction):
    """Construct one assignment for fixed/add/subgroup/binding actual rows.

    Existing strict metadata/row plans supply every source role and write list.
    The intentionally narrow pinned column specialization refuses a different
    allocation. Named codec/SDK/standard group contracts remain global and
    independent of the constructed circuit output. Earlier IVK/ownership/hash
    row construction is a separate dependency, not an assumed final row fact.
    """
    from . import generate_transfer_rk_sdk as sdk
    from . import transfer_rk_point_add as point_add
    from .generate_transfer_rk_subgroup import completion_plan
    from .generate_transfer_rnk_frame import extend_rk_support
    owned=sdk.generate_full_owned_inputs(captures,accepted_roles,extractions)
    normalized=re.sub(r'\s+','',owned)
    if 'definputColumns:ListNat:=[1980,1981,3766]' not in normalized:
        raise RelationError('exact owned fixed authorization input roles')
    obj,points,*_=point_add.selection(authorization_data,accepted_roles,addition_extraction)
    expected={'ak':(((1980,1),),((1981,1),)),
        'contribution':(((4269,1),),((4270,1),)),
        'computed':(((64456,1),),((64460,1),))}
    plan=completion_plan(subgroup_data,accepted_roles,subgroup_extraction)
    state=plan['state']
    public=tuple(state['derived'][handle] for handle in state['inputs'][:2])
    if (points!=expected or obj['constant_copy']!=200692 or
            public!=(((4272,1),),((4273,1),)) or
            subgroup_extraction['allocation']['witnesses']!=list(range(4274,4280))):
        raise RelationError('exact captured authorization endpoint allocation required')
    support=sdk.generate_support(authorization_data,accepted_roles,addition_extraction,
        subgroup_data,subgroup_extraction,high_start=22738)
    extend_rk_support(support) # strict current allocation/frame guards, no acceptance
    source=_OWNED_JOIN
    aliases={'OWN':'RuntimeTransferOwnedFixedInputs','FIX':'RuntimeTransferFixedSpend',
        'FULL':'RuntimeTransferFixedSpendCompletion','ADD':'RuntimeTransferRkAdditionCompletion',
        'AROW':'RuntimeTransferRkAddition','SUB':'RuntimeTransferRkSubgroupCompletion',
        'SDK':'RuntimeTransferRkSdkCompletion','MAT':'RuntimeTransferRkSubgroupMaterialization',
        'SUP':'RuntimeTransferRkSupport','BIND':'RuntimeTransferRkBinding'}
    for short,module in aliases.items():source=source.replace(short+'.',module+'.')
    return source


_OWNED_JOIN='''import ShielddSecurity.RuntimeTransferOwnedFixedInputs
import ShielddSecurity.RuntimeTransferFixedSpend_Frame
import ShielddSecurity.RuntimeTransferRkSupport
import ShielddSecurity.RuntimeTransferRkBinding
import ShielddSecurity.GroupFrameTransport
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferOwnedAuthorizationCompletion

variable {F E S R K Q Signing J Encoded Native : Type} [Field F]
  [CharP F Scalar.modulus] [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J (FIX.coefficientD : F)}

private theorem fixed_rows_later_covered : GroupFixedCircuitBounds.RowsCovered
    22738 200692 SUP.additionFrame FIX.rawRows := by
  intro row member term present
  rcases RuntimeTransferFixedSpend_Frame.rows_covered row member term present with low | high | copied
  · exact Or.inl (Nat.lt_trans low (by decide))
  · exact Or.inr (Or.inl ⟨high.1,Nat.lt_trans high.2 (by decide)⟩)
  · exact Or.inr (Or.inr copied)

/-- Transport uses actual finite support/write certificates, without guessing
compiler origins or relying on a desired later assignment. -/
theorem subgroup_preserves_constructed_rows
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr (FIX.coefficientD : F) model)
    (base : Nat → F) (point : S) (prior : List Row)
    (covered : GroupFixedCircuitBounds.RowsCovered 22738 200692 SUP.additionFrame prior)
    (constructed : Satisfies base prior) :
    Satisfies (SUB.assignment (SDK.publicBase base sdk point) codec writer
      (model.coordinates (sdk.embed (sdk.promote point)))) prior := by
  have publicOutside : ∀ column ∈ SDK.publicColumns,
      ¬GroupFixedCircuitBounds.covers 22738 200692 SUP.additionFrame column := by
    intro column member
    exact SUP.patches_outside column (List.mem_append.mpr (Or.inl member))
  have witnessOutside : ∀ column ∈ SUB.witnessColumns,
      ¬GroupFixedCircuitBounds.covers 22738 200692 SUP.additionFrame column := by
    intro column member
    exact SUP.patches_outside column (List.mem_append.mpr (Or.inr member))
  have publicRows := GroupFrameTransport.patch_preserves_rows base (SDK.publicValues sdk point)
    SDK.publicColumns 22738 200692 SUP.additionFrame prior covered publicOutside constructed
  have witnessRows := GroupFrameTransport.patch_preserves_rows (SDK.publicBase base sdk point)
    (SUB.witnessValues codec writer (model.coordinates (sdk.embed (sdk.promote point))))
    SUB.witnessColumns 22738 200692 SUP.additionFrame prior covered witnessOutside publicRows
  exact GroupFrameTransport.run_preserves_rows _ MAT.steps 22738 200692 SUP.additionFrame
    prior covered SUP.subgroup_outside witnessRows

def construct (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr (FIX.coefficientD : F) model)
    (base : Nat → F) (actionPoint randomizedPoint : S) (randomizer : R) : Nat → F :=
  let initial := OWN.seed base upstream actionPoint randomizer
  let fixed := FULL.construct initial (fr.integer randomizer)
  let added := ADD.completeAssignment fixed
  SUB.assignment (SDK.publicBase added (ShielddNativeSdk.sdk upstream) randomizedPoint) codec writer
    (model.coordinates (upstream.embed (upstream.promote randomizedPoint)))

/-- All four row families hold in the same explicit assignment. No local
fixed meanings, desired native coordinates, subgroup output or row truth is
assumed. External compressed admissions and global standard/codec contracts
remain explicit and do not mention any circuit assignment. -/
theorem actual_owned_authorization_rows_complete
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr (FIX.coefficientD : F) model)
    (standard : OWN.StandardSpendAuth upstream)
    (base : Nat → F) (verification : K) (randomizer : R) (actionPoint randomizedPoint : S)
    (actionAdmission : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) = some actionPoint)
    (randomizedAdmission : ShielddNativeSdk.nonidentity upstream
      (upstream.keyBytes (ShielddNativeSdk.planRk upstream verification randomizer)) = some randomizedPoint)
    (one : base 0 = 1) (linked : base 200692 = base 0) (four : (4 : F) ≠ 0)
    (two : (2 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (FIX.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    let completed := construct codec writer upstream base actionPoint randomizedPoint randomizer
    Satisfies completed FIX.rawRows ∧
      Satisfies completed AROW.rawRows ∧
      Satisfies completed SUB.rawRows ∧
      Satisfies completed BIND.rawRows ∧
      ShielddNativeAuthorization.authorization backend upstream codec writer verification randomizer =
        some (BIND.computed completed) := by
  dsimp only
  let initial := OWN.seed base upstream actionPoint randomizer
  let fixed := FULL.construct initial (fr.integer randomizer)
  let added := ADD.completeAssignment fixed
  let completed := construct codec writer upstream base actionPoint randomizedPoint randomizer
  have fixedRows := OWN.owned_fixed_rows_complete upstream base actionPoint randomizer one four linked
    imaginary nonSquare imaginarySquare
  have fixedNative := OWN.owned_fixed_native_complete codec upstream standard base actionPoint randomizer
    one four linked imaginary nonSquare imaginarySquare
  have legalAction := GroupNativeSdk.admitted_key (ShielddNativeSdk.sdk upstream)
    verification actionPoint actionAdmission
  have keySeed : OWN.actionKey initial = model.coordinates (upstream.embed (upstream.promote actionPoint)) := by
    rw [upstream.affineMeaning]
    simp [initial,OWN.actionKey,OWN.seed,OWN.inputValues,OWN.inputColumns,patchAssignment,
      ShielddNativeSdk.coordinateX,ShielddNativeSdk.coordinateY]
  have keyRole : ADD.actionKey fixed = model.coordinates (upstream.embed (upstream.keyPoint verification)) := by
    have same : OWN.actionKey fixed = OWN.actionKey initial := fixedRows.2.2.2.1
    simpa only [ADD.actionKey,OWN.actionKey,eval,Int.cast_one,one_mul,add_zero] using
      same.trans (keySeed.trans (congrArg model.coordinates legalAction.1))
  have contributionRole : ADD.fixedContribution fixed = model.coordinates
      (fr.integer randomizer • upstream.embed (upstream.promote upstream.spendAuthSubgroup)) := by
    simpa only [ADD.fixedContribution,FIX.contribution,RuntimeFixedSpendChunk112.output,
      RuntimeFixedSpendWindow125.output] using fixedNative.2
  have zeroFixed : fixed 0 = base 0 := fixedRows.2.2.2.2 0 (by decide)
  have copyFixed : fixed 200692 = base 200692 := fixedRows.2.2.2.2 200692 (by decide)
  have fixedOne : fixed 0 = 1 := zeroFixed.trans one
  have fixedLink : fixed 200692 = fixed 0 := copyFixed.trans (linked.trans zeroFixed.symm)
  have addition := ADD.actual_addition_complete fixed fixedOne four imaginary nonSquare imaginarySquare fixedLink
    (by rw [keyRole]; exact model.onCurve _)
    (by rw [contributionRole]; exact model.onCurve _)
  have computed := ADD.actual_addition_group_complete fixed fixedOne four imaginary model nonSquare
    imaginarySquare fixedLink _ _ keyRole contributionRole
  have addedFixed : Satisfies added FIX.rawRows := GroupFrameTransport.run_preserves_rows fixed
    ADD.completionSteps 22738 200692 SUP.fixedFrame FIX.rawRows
    RuntimeTransferFixedSpend_Frame.rows_covered SUP.addition_outside fixedRows.1
  have addedOne : added 0 = 1 := (addition.2.2 0 (by decide)).trans fixedOne
  have addedLink : added 200692 = added 0 :=
    (addition.2.2 200692 (by decide)).trans (fixedLink.trans (addition.2.2 0 (by decide)).symm)
  have subgroup := SDK.actual_owned_randomized_public_rows_complete codec writer backend upstream
    imaginary nonSquare imaginarySquare two added verification randomizer actionPoint randomizedPoint
    actionAdmission randomizedAdmission addedOne addedLink
  have subgroupRows : Satisfies completed SUB.rawRows := subgroup.2.2.2.1
  have protected : ∀ column ∈ SDK.protectedColumns, completed column = added column := subgroup.2.2.2.2
  have finalFixed : Satisfies completed FIX.rawRows := subgroup_preserves_constructed_rows codec writer
    (ShielddNativeSdk.sdk upstream) added randomizedPoint FIX.rawRows fixed_rows_later_covered addedFixed
  have finalAddition : Satisfies completed AROW.rawRows := subgroup_preserves_constructed_rows codec writer
    (ShielddNativeSdk.sdk upstream) added randomizedPoint AROW.rawRows SUP.addition_rows_covered addition.1
  have computedKept : BIND.computed completed = AROW.computed added := by
    apply congrArg₂ Group.Point.mk
    · simpa only [BIND.computed,BIND.computedX,AROW.computed,eval,
        Int.cast_one,one_mul,add_zero] using protected 64456 (by decide)
    · simpa only [BIND.computed,BIND.computedY,AROW.computed,eval,
        Int.cast_one,one_mul,add_zero] using protected 64460 (by decide)
  have legalRandomized := GroupNativeSdk.admitted_key (ShielddNativeSdk.sdk upstream)
    (ShielddNativeSdk.planRk upstream verification randomizer) randomizedPoint randomizedAdmission
  have randomizedRole : BIND.computed completed =
      model.coordinates (upstream.embed (upstream.promote randomizedPoint)) := by
    rw [computedKept,computed,←ShielddNativeSdk.plan_randomization upstream verification randomizer]
    exact congrArg model.coordinates legalRandomized.1.symm
  have publicRole : BIND.rk completed = model.coordinates (upstream.embed (upstream.promote randomizedPoint)) := by
    have xKept := SUB.caller_preserved (SDK.publicBase added (ShielddNativeSdk.sdk upstream) randomizedPoint)
      codec writer (model.coordinates (upstream.embed (upstream.promote randomizedPoint))) 4272 (by decide)
    have yKept := SUB.caller_preserved (SDK.publicBase added (ShielddNativeSdk.sdk upstream) randomizedPoint)
      codec writer (model.coordinates (upstream.embed (upstream.promote randomizedPoint))) 4273 (by decide)
    rw [upstream.affineMeaning]
    simp only [BIND.rk,BIND.rkX,BIND.rkY,eval,Int.cast_one,one_mul,add_zero]
    apply congrArg₂ Group.Point.mk
    · exact xKept.trans (by simp [SDK.publicBase,SDK.publicValues,SDK.publicColumns,patchAssignment,ShielddNativeSdk.sdk])
    · exact yKept.trans (by simp [SDK.publicBase,SDK.publicValues,SDK.publicColumns,patchAssignment,ShielddNativeSdk.sdk])
  have equal : BIND.computed completed = BIND.rk completed := randomizedRole.trans publicRole.symm
  have xEqual : completed 64456 = completed 4272 := by
    simpa only [BIND.computed,BIND.computedX,BIND.rk,BIND.rkX,eval,Int.cast_one,one_mul,add_zero] using congrArg Group.Point.x equal
  have yEqual : completed 64460 = completed 4273 := by
    simpa only [BIND.computed,BIND.computedY,BIND.rk,BIND.rkY,eval,Int.cast_one,one_mul,add_zero] using congrArg Group.Point.y equal
  have finalOne : completed 0 = 1 := (protected 0 (by decide)).trans addedOne
  have finalLink : completed 200692 = completed 0 :=
    (protected 200692 (by decide)).trans (addedLink.trans (protected 0 (by decide)).symm)
  have bindingRows : Satisfies completed BIND.rawRows := by
    intro row member
    simp only [BIND.rawRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [Square,eval,Int.cast_neg,Int.cast_one,xEqual,yEqual,finalLink] <;> ring
  have native := ShielddNativeAuthorization.owned_authorization_coordinates codec writer backend upstream
    imaginary nonSquare imaginarySquare two verification randomizer actionPoint actionAdmission
  refine ⟨finalFixed,finalAddition,subgroupRows,bindingRows,?_⟩
  exact native.trans (congrArg some (computedKept.trans computed).symm)

set_option pp.all true in
#check @subgroup_preserves_constructed_rows
#print axioms subgroup_preserves_constructed_rows
set_option pp.all true in
#check @actual_owned_authorization_rows_complete
#print axioms actual_owned_authorization_rows_complete
end ShielddSecurity.RuntimeTransferOwnedAuthorizationCompletion
'''
