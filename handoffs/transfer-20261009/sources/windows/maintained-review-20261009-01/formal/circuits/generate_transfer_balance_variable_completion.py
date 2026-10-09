"""Strict balance129 consumers of neutral owned local construction renderers.

The 252-bit ownership parser/default generator API remains unchanged. This
adapter accepts the actual 129-bit reversed pair and the first native false
padding operand. Local curve construction derives division legality; native
base/signed magnitude/all65 sequencing are separate explicit joins.
"""
from . import transfer_balance_variable as variable,transfer_balance_variable_batch as batch
from . import transfer_balance_variable_completion as completion
from . import transfer_relation as relation
from . import generate_transfer_ownership_completion as mixed
from . import generate_transfer_ownership_point_materializations as material
from . import generate_transfer_ownership_double_completion as point
from . import generate_transfer_ownership_selector_completion as selector
from . import generate_transfer_ownership_window_curve_completion as curve
from . import generate_transfer_ownership_folded_window_completion as folded
from . import generate_transfer_ownership_folded_window_curve as folded_curve
from . import generate_transfer_ownership_native_seed as native_seed
from . import generate_transfer_ownership_precompute_native as precompute
from . import generate_transfer_balance_variable_tables as native_tables
from .generate_hash_round import linear,_signature_audits


PREFIX='RuntimeBalanceVariableWindow'


def _checked(checked,window_offset):
    metadata=checked.get('metadata',{}) if isinstance(checked,dict) else {}
    if (metadata.get('schema')!='shieldd-transfer-balance-variable-v1' or
            metadata.get('bit_width')!=129 or metadata.get('total_windows')!=65 or
            type(window_offset)is not int or not 0<=window_offset<len(checked.get('windows',[]))):
        raise relation.RelationError('balance129 constructor strict local source schema/index')
    # The source checker rechecks native-false padding and all formula operands;
    # it does not rewrite the captured schema as ownership252.
    variable.match_formulas(checked)


def generate_window(checked,extracted,window_offset,readonly_lcs=()):
    """Exact local constructor; no desired point/inverse/row truth is an input."""
    _checked(checked,window_offset)
    plan=completion.window_plan(checked,extracted,window_offset,False,readonly_lcs)
    cones=completion.cone_certificates(checked,extracted,window_offset,False)
    modules=[mixed.render_plan(checked,extracted,plan,PREFIX)]
    modules.extend(material.render_points(checked,plan,cones,PREFIX))
    observe=lambda value:checked['derived'][value[1]] if value[0]=='source' else completion.canonical([(0,value[1])])
    pair=tuple(map(observe,checked['window_bits'][window_offset]))
    if plan['window_index']==0:
        local=folded.render_folded(checked,extracted,plan,PREFIX)
        modules.append(local)
        modules.append(_formula(folded_curve.render_folded_curve(checked,plan,cones,local[0],pair,native_inputs=True),plan,window_offset,checked))
    else:
        for group in plan['point_groups']:
            modules.append(point.render_point(checked,extracted,plan,cones,group['index'],PREFIX))
        modules.append(selector.render_selector(checked,plan,cones,window_offset,PREFIX,pair,native_inputs=True))
        modules.append(_formula(curve.render_window(checked,plan,window_offset,PREFIX),plan,window_offset,checked))
    return modules


def _formula(module,plan,window_offset,checked):
    """Retain local construction's affine recurrence for native loop induction.

    This appends a maintained template in the new balance namespace. It never
    changes the original ownership module or an emitted candidate on disk.
    """
    name,source=module;stem=PREFIX+f'{plan["window_index"]:03d}';copy=checked['metadata']['constant_copy']
    if plan['window_index']==0:
        local=stem+'FoldedCompletion';material=stem+'Point4Materializations'
        theorem=f'''theorem actual_window_formula {{F : Type}} [Field F] [CharP F {local}.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = base 0) :
    output ({local}.completeAssignment base) = Group.windowPoint (eval base low) (eval base high)
      (basePoint base) (twicePoint base) (triplePoint base) :=
  (selected_output base).trans (material_selected base one linked)
#print axioms actual_window_formula
'''
    else:
        start=source.index('theorem actual_window_complete ')
        boundary=source.index(' :\n    Satisfies ',start)
        body_start=source.index(' := by\n',boundary)+len(' := by\n')
        body_end=source.index('  have earlierSecond :',body_start)
        header=source[start:boundary].replace('theorem actual_window_complete','theorem actual_window_formula',1)
        d0=stem+f'Point{2+3*window_offset}Completion';d1=stem+f'Point{3+3*window_offset}Completion'
        add=stem+f'Point{4+3*window_offset}Completion';selector=stem+f'Point{4+3*window_offset}SelectorCompletion'
        material=stem+f'Point{4+3*window_offset}Materializations'
        doubled=f'(Group.affineAdd (d : F) ({d0}.inputPoint base) ({d0}.inputPoint base))'
        theorem=header+f''' :
    {add}.outputPoint (completeAssignment base) = Group.affineAdd (d : F)
      (Group.affineAdd (d : F) {doubled} {doubled})
      (Group.windowPoint (eval base {selector}.low) (eval base {selector}.high)
        ({selector}.basePoint base) ({selector}.twicePoint base) ({selector}.triplePoint base)) := by
'''+source[body_start:body_end]+f'''  have firstCoordinates : {d1}.inputPoint (afterFirst base) = {doubled} := by
    rw [second_input]
    exact first.2.1
  have secondCoordinates : {add}.inputPoint (beforeAdd base) =
      Group.affineAdd (d : F) {doubled} {doubled} := by
    rw [add_input]
    have coordinates := second.2.1
    change {d1}.outputPoint (beforeAdd base) = Group.affineAdd (d : F)
      ({d1}.inputPoint (afterFirst base)) ({d1}.inputPoint (afterFirst base)) at coordinates
    rw [firstCoordinates] at coordinates
    exact coordinates
  have selectedCoordinates := {selector}.material_selected (beforeAdd base) nextOne nextLink
  rw [eval_before_add base linked {selector}.low (by decide) (by decide),
    eval_before_add base linked {selector}.high (by decide) (by decide),
    basePreserved,twicePreserved,triplePreserved] at selectedCoordinates
  have rightCoordinates : {add}.rightPoint ({material}.materialAssignment (beforeAdd base)) =
      Group.windowPoint (eval base {selector}.low) (eval base {selector}.high)
        ({selector}.basePoint base) ({selector}.twicePoint base) ({selector}.triplePoint base) := by
    rw [selected_input]
    exact selectedCoordinates
  exact added.2.1.trans (congrArg₂ (Group.affineAdd (d : F)) secondCoordinates rightCoordinates)
#print axioms actual_window_formula
'''
    ending=f'end ShielddSecurity.{name}\n'
    if not source.endswith(ending):raise relation.RelationError('balance129 exact maintained constructor ending')
    return name,_signature_audits(source[:-len(ending)]+theorem+ending)


def generate_precompute(checked,extracted,readonly_lcs=()):
    """Seed the actual table from a native reader, then construct double/add.

    This uses the existing SDK reader/coordinate seed functional contract.
    Same balance.assetGenerator/native object association is a later source
    join; it is not inferred from a source handle or packet hash.
    """
    _checked(checked,0)
    if checked['metadata']['window_start']!=0:
        raise relation.RelationError('balance129 native precompute only first page')
    whole=completion.window_plan(checked,extracted,0,True,readonly_lcs)
    cones=completion.cone_certificates(checked,extracted,0,True)
    groups=[group for group in whole['point_groups'] if group['index'] in (0,1)]
    if len(groups)!=2:raise relation.RelationError('balance129 exact two native table operations')
    plan=dict(whole,point_groups=groups)
    modules=material.render_points(checked,plan,cones,PREFIX)
    d=point.render_point(checked,extracted,plan,cones,0,PREFIX)
    a=point.render_point(checked,extracted,plan,cones,1,PREFIX)
    n=native_seed.render_seed(checked,cones,d[0])
    table=precompute.render_precompute(checked,plan,cones,d[0],a[0],n[0])
    modules.extend([d,a,n,native_tables.augment(table,checked,plan,d[0],a[0],n[0])])
    return modules


def generate_page(qualified_parent,raw_pages,expected_relation,expected_signed,expected_base,
        extracted,page_ordinal,readonly_lcs=()):
    """Bounded callable after the genuine five-page qualifier and one replay."""
    checked=variable.inspect_pages(qualified_parent,raw_pages,expected_relation,expected_signed,expected_base)
    relation.natural(page_ordinal,5)
    selection=batch.page_selection(checked,extracted,page_ordinal)
    page=checked['chunks'][page_ordinal]
    seen=set()
    if page_ordinal==0:
        for item in generate_precompute(page,selection,readonly_lcs):
            seen.add(item[0]);yield item
    for offset in range(page['metadata']['window_count']):
        for item in generate_window(page,selection,offset,readonly_lcs):
            if item[0] in seen:raise relation.RelationError('balance129 duplicate local constructor namespace')
            seen.add(item[0]);yield item


def render_program(checked,extracted,window_offset,readonly_lcs=(),*,compiler_origin=22738,sequence_kept=None):
    """Bounded variable65 program interface; numeric frames come from owned rows."""
    _checked(checked,window_offset)
    relation.natural(compiler_origin,checked['metadata']['domain_size'])
    plan=completion.window_plan(checked,extracted,window_offset,False,readonly_lcs)
    if sequence_kept is not None:
        if (not isinstance(sequence_kept,list) or sequence_kept!=sorted(set(sequence_kept)) or
                len(sequence_kept)>4096 or any(type(column)is not int or
                not 0<=column<checked['metadata']['domain_size'] for column in sequence_kept) or
                set(sequence_kept)&set(plan['writes'])):
            raise relation.RelationError('balance129 sequence kept/write source separation')
    observe=lambda value:checked['derived'][value[1]] if value[0]=='source' else completion.canonical([(0,value[1])])
    before=[c for c in plan['writes'] if c<compiler_origin]
    after=[c for c in plan['writes'] if compiler_origin<=c<checked['metadata']['constant_copy']]
    if not before or not after or set(plan['writes'])&{0,1,2,checked['metadata']['constant_copy']}:
        raise relation.RelationError('balance129 program exact disjoint dual allocation frames')
    stem=PREFIX+f'{plan["window_index"]:03d}';first=plan['window_index']==0
    constructor=stem+('FoldedCurveCompletion' if first else 'CurveCompletion')
    runner=stem+'FoldedCompletion' if first else constructor
    steps=runner+('.completionSteps' if first else '.steps')
    bits=constructor if first else stem+f'Point{4+3*window_offset}SelectorCompletion'
    name=stem+'Program';copy=checked['metadata']['constant_copy']
    pair=lambda roles:'('+','.join(linear(observe(value)) for value in roles)+')'
    tables=','.join(pair(checked['points'][key]) for key in ('base','twice','triple'))
    incoming=pair(checked['windows'][window_offset][0]);outgoing=pair(checked['windows'][window_offset][4])
    d=stem+'Point4Cones.coefficientD' if first else constructor+'.d'
    source=f'''import ShielddSecurity.{constructor}
import ShielddSecurity.{stem}Completion
import ShielddSecurity.GroupVariableCircuitCompletion
import ShielddSecurity.GroupVariableCircuitNative
import ShielddSecurity.GroupFixedCircuitBounds
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def tables : GroupVariableCircuitCompletion.Tables := ⟨{tables}⟩
def beforeFrame : GroupFixedCircuitBounds.Frame := ⟨{min(before)},{min(after)}⟩
def afterFrame : GroupFixedCircuitBounds.Frame := ⟨{max(before)+1},{max(after)+1}⟩
def program (lowBit highBit : Bool) : GroupFixedCircuitCompletion.Program :=
  ⟨{steps},{runner}.rawRows,{incoming},{outgoing},{bits}.low,{bits}.high,lowBit,highBit⟩
theorem checked_bounds (lowBit highBit : Bool) :
    GroupFixedCircuitBounds.checkLocal {compiler_origin} {copy} beforeFrame afterFrame
      (program lowBit highBit) = true := by
  cases lowBit <;> cases highBit <;> decide
theorem original_rows_covered (lowBit highBit : Bool) :
    ∀ row ∈ {stem}Completion.rawRows, row ∈ (program lowBit highBit).rows := by
  have checked : {stem}Completion.rawRows.all (fun row => decide (row ∈ {runner}.rawRows)) = true := by decide
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp checked row member)
theorem outside {{F : Type}} [Field F] (base : Nat → F) (lowBit highBit : Bool)
    (column : Nat) (fresh : column ∉ GroupCircuitSequenceCompletion.writes {steps}) :
    (program lowBit highBit).build base column = base column :=
  GroupCircuitSequenceCompletion.run_preserves base {steps} column fresh
theorem local_constructor {{F : Type}} [Field F] [CharP F {runner}.modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({d} : F))
    (imaginarySquare : imaginary*imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitCompletion.LocalConstruct ({d} : F) {copy} tables (program lowBit highBit) := by
  intro base one linked incoming curved lowValue highValue
'''
    if first:
        source+=f'''  have result := {constructor}.actual_window_complete base one linked lowBit highBit lowValue highValue
    curved.1 curved.2.1 curved.2.2
  simpa only [program,GroupFixedCircuitCompletion.Program.build,{runner}.completeAssignment,
    GroupFixedCircuitCompletion.point,{constructor}.output,eval,Int.cast_one,one_mul,add_zero] using result
'''
    else:
        added=stem+f'Point{4+3*window_offset}Completion'
        source+=f'''  have result := {constructor}.actual_window_complete base one linked imaginary nonSquare imaginarySquare
    lowBit highBit incoming lowValue highValue curved.1 curved.2.1 curved.2.2
  simpa only [program,GroupFixedCircuitCompletion.Program.build,{runner}.completion_factor,
    GroupFixedCircuitCompletion.point,{added}.outputPoint,GroupQuotientPairCompletion.point,
    {added}.x,{added}.y,eval,Int.cast_one,one_mul,add_zero] using result
'''
    source+=f'''theorem local_formula {{F : Type}} [Field F] [CharP F {runner}.modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({d} : F))
    (imaginarySquare : imaginary*imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitNative.LocalFormula ({d} : F) {copy} tables (program lowBit highBit) := by
  intro base one linked incoming curved lowValue highValue
'''
    if first:
        source+=f'''  have result := {constructor}.actual_window_formula base one linked
  have inputIdentity : GroupFixedCircuitCompletion.point base (program lowBit highBit).input =
      Group.identityPoint := by
    simp only [program,GroupFixedCircuitCompletion.point,Group.identityPoint,eval,
      List.map_nil,List.sum_nil,List.map_cons,List.sum_cons,Int.cast_one,one_mul,add_zero,one]
  change GroupFixedCircuitCompletion.point ((program lowBit highBit).build base)
    (program lowBit highBit).output = _
  rw [inputIdentity,GroupVariableCircuitNative.affine_identity_left,
    GroupVariableCircuitNative.affine_identity_left,GroupVariableCircuitNative.affine_identity_left]
  simpa only [program,tables,GroupFixedCircuitCompletion.Program.build,{runner}.completeAssignment,
    GroupFixedCircuitCompletion.point,{constructor}.output,{constructor}.basePoint,
    {constructor}.twicePoint,{constructor}.triplePoint,
    {constructor}.baseX,{constructor}.baseY,{constructor}.twiceX,{constructor}.twiceY,
    {constructor}.tripleX,{constructor}.tripleY,
    eval,Int.cast_one,one_mul,add_zero] using result
'''
    else:
        selector_name=stem+f'Point{4+3*window_offset}SelectorCompletion'
        source+=f'''  have result := {constructor}.actual_window_formula base one linked imaginary nonSquare imaginarySquare
    lowBit highBit incoming lowValue highValue curved.1 curved.2.1 curved.2.2
  simpa only [program,tables,GroupFixedCircuitCompletion.Program.build,{runner}.completion_factor,
    GroupFixedCircuitCompletion.point,{added}.outputPoint,GroupQuotientPairCompletion.point,
    {added}.x,{added}.y,{stem}Point{2+3*window_offset}Completion.inputPoint,
    {stem}Point{2+3*window_offset}Completion.inputX,{stem}Point{2+3*window_offset}Completion.inputY,
    {selector_name}.basePoint,{selector_name}.twicePoint,{selector_name}.triplePoint,
    {selector_name}.baseX,{selector_name}.baseY,{selector_name}.twiceX,{selector_name}.twiceY,
    {selector_name}.tripleX,{selector_name}.tripleY,
    eval,Int.cast_one,one_mul,add_zero] using result
'''
    for export in ('checked_bounds','original_rows_covered','outside','local_constructor','local_formula'):
        source+='#print axioms '+export+'\n'
    if sequence_kept is not None:
        source+=f'''def sequenceKept : List Nat := {sequence_kept}
theorem sequence_protected (lowBit highBit : Bool) :
    GroupFixedCircuitCompletion.Protected sequenceKept (program lowBit highBit) := by
  have checked : {steps}.all
    (fun stage => GroupCircuitOrder.checkOutside sequenceKept stage.writes) = true := by decide
  intro stage member column present written
  exact (of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column written)) present
#print axioms sequence_protected
'''
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
