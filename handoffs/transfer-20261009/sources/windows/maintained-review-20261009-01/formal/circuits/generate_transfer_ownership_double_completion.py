"""Construct the exact first optimized double after its materialized cones.

The incoming source point's curve membership is an independent local input
contract. A whole ownership loop must derive that contract from its admitted
base and preceding curve closure. No quotient value or row truth is assumed.
"""
from . import transfer_ownership_completion as completion
from .generate_hash_round import linear, _signature_audits
from .generate_transfer_ownership_completion import lower_stage


def generate(checked, extracted, readonly_lcs=()):
    return _generate(checked, extracted, readonly_lcs, 0)


def generate_window_double(checked, extracted, window_offset, double_number, readonly_lcs=()):
    """One actual nonfolded optimized double, after its constructed incoming point.

    The first window's native identity doubles are handled by the exact folded
    constructor. All later doubles must own the actual two quotient coordinates.
    """
    if type(window_offset) is not int or not 0 <= window_offset < len(checked['windows']) or \
            type(double_number) is not int or double_number not in (0, 1):
        raise completion.relation.RelationError('ownership typed bounded window double selection')
    return _generate(checked, extracted, readonly_lcs, 2+3*window_offset+double_number,
                     window_offset, False)


def _generate(checked, extracted, readonly_lcs, point_index, window_offset=0, include_precompute=True):
    """Shared exact-row renderer; no accepted observation is rewritten."""
    if type(point_index) is not int or point_index < 0:
        raise completion.relation.RelationError('ownership precompute point selection')
    plan = completion.window_plan(checked, extracted, window_offset, include_precompute, readonly_lcs)
    cones = completion.owner.cone_certificates(checked, extracted, window_offset, include_precompute)
    prefix = 'RuntimeRnkWindow' if checked['metadata'].get('schema') == 'shieldd-transfer-rnk-dh-v1' else 'RuntimeOwnershipWindow'
    return render_point(checked,extracted,plan,cones,point_index,prefix)


def render_point(checked,extracted,plan,cones,point_index,prefix):
    """Neutral original quotient/cone renderer after a strict ingress plan."""
    import re
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',prefix) is None:
        raise completion.relation.RelationError('point completion namespace')
    matches = [group for group in plan['point_groups'] if group['index'] == point_index]
    if len(matches) != 1:
        raise completion.relation.RelationError('ownership unique actual point operation')
    group = matches[0]
    addition = group['kind'] == 'add'
    constructed_selector = addition and group.get('formula_count', 4) == 6
    stages = plan['stages'][group['material_end']:group['stage_end']]
    if group['index'] != point_index or group['kind'] != ('add' if addition else 'double') or len(stages) != 2 or any(
            stage['kind'] != 'quotient' for stage in stages):
        raise completion.relation.RelationError('ownership precompute exact two nonlinear coordinates')
    first = group.get('formula_start', 4*point_index)
    selected = [next(cone for cone in cones['cones'] if cone['role']=='formula'+str(i))
                for i in range(first,first+4)]
    inputs = [cones['observations'][identity][1] for identity in selected[0]['inputs']]
    if len(inputs) != (4 if addition else 2) or any([cones['observations'][identity][1] for identity in cone['inputs']] != inputs
                             for cone in selected):
        raise completion.relation.RelationError('ownership precompute exact shared source input LCs')
    for stage, numerator, denominator in ((stages[0], selected[0], selected[2]),
                                          (stages[1], selected[1], selected[3])):
        if stage['numerator'] != cones['observations'][numerator['output']][1] or \
                stage['denominator'] != cones['observations'][denominator['output']][1]:
            raise completion.relation.RelationError('ownership precompute coordinate exact formula endpoints')
    stem=prefix+f'{plan["window_index"]:03d}Point{point_index}';c=stem+'Cones';m=stem+'Materializations';name=stem+'Completion'
    copy=checked['metadata']['constant_copy'];p=completion.relation.MODULUS
    def coordinate(stage):
        return '⟨'+','.join([linear(stage[key]) for key in ('numerator','denominator','remainder')]+
            [str(stage[key]) for key in ('quotient','product','auxiliary')])+'⟩'
    indices=sorted(index for stage in stages for index in stage['rows'])
    raw={row['row']:row for row in extracted['selected_rows']}
    row_literals=['⟨'+','.join(linear(tuple((column,int(value,16)) for column,value in raw[index][key]))
                  for key in ('a','b'))+'⟩' for index in indices]
    extra_inputs = (f'''def rightX : Linear := {linear(inputs[2])}
def rightY : Linear := {linear(inputs[3])}
def rightPoint {{F : Type}} [Field F] (base : Nat → F) : Group.Point F := ⟨eval base rightX,eval base rightY⟩
''' if addition else '')
    preserved_statement = (f'''inputPoint ({m}.materialAssignment base) = inputPoint base ∧
      rightPoint ({m}.materialAssignment base) = rightPoint base''' if addition and not constructed_selector else
        f'inputPoint ({m}.materialAssignment base) = inputPoint base')
    preserved_proof = (f'''  constructor
  · exact congrArg₂ Group.Point.mk (agrees inputX (by simp [inputX,{m}.kept]))
      (agrees inputY (by simp [inputY,{m}.kept]))
  · exact congrArg₂ Group.Point.mk (agrees rightX (by simp [rightX,{m}.kept]))
      (agrees rightY (by simp [rightY,{m}.kept]))
''' if addition and not constructed_selector else f'''  exact congrArg₂ Group.Point.mk (agrees inputX (by simp [inputX,{m}.kept]))
    (agrees inputY (by simp [inputY,{m}.kept]))
''')
    source=f'''import ShielddSecurity.{m}
import ShielddSecurity.GroupQuotientPairCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {p}
def x : GroupQuotientPairCompletion.Coordinate := {coordinate(stages[0])}
def y : GroupQuotientPairCompletion.Coordinate := {coordinate(stages[1])}
def inputX : Linear := {linear(inputs[0])}
def inputY : Linear := {linear(inputs[1])}
def inputPoint {{F : Type}} [Field F] (base : Nat → F) : Group.Point F := ⟨eval base inputX,eval base inputY⟩
{extra_inputs}def completed {{F : Type}} [Field F] (base : Nat → F) : Nat → F :=
  GroupQuotientPairCompletion.build x y ({m}.materialAssignment base)
def outputPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := GroupQuotientPairCompletion.point x y rho
def quotientIndices : List Nat := {indices}
def quotientRaw : List Row := ['''+',\n'.join(row_literals)+f''']
private theorem shapeX : x.Shape := by
  simp [x,GroupQuotientPairCompletion.Coordinate.Shape,GroupQuotientPairCompletion.Coordinate.inputs,
    GroupQuotientPairCompletion.Coordinate.writes,GroupRowCompletion.writes]
private theorem shapeY : y.Shape := by
  simp [y,GroupQuotientPairCompletion.Coordinate.Shape,GroupQuotientPairCompletion.Coordinate.inputs,
    GroupQuotientPairCompletion.Coordinate.writes,GroupRowCompletion.writes]
private theorem separate : ∀ term ∈ y.inputs, term.1 ∉ x.writes := by
  have checked : y.inputs.all (fun term => decide (term.1 ∉ x.writes)) = true := by decide
  intro term member; exact of_decide_eq_true (List.all_eq_true.mp checked term member)
private theorem fresh : ∀ row ∈ x.rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ y.writes := by
  have checked : x.rows.all (fun row => (row.a ++ row.b).all (fun term => decide (term.1 ∉ y.writes))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
theorem input_preserved {{F : Type}} [Field F] [CharP F modulus] (base : Nat → F)
    (linked : base {copy} = base 0) :
    {preserved_statement} := by
  have kept := ({m}.material_rows_complete base linked).2
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term.1 ∈ {m}.kept) :
      eval ({m}.materialAssignment base) terms = eval base terms := by
    apply eval_agrees; intro term member; exact kept term.1 (inside term member)
{preserved_proof}'''
    descriptions=(('numerator_x','x.numerator',0,'GroupExtended.doubleNumerator'),
                  ('numerator_y','y.numerator',1,'fun point : Group.Point F => Group.diagonal point point'),
                  ('denominator_x','x.denominator',2,'GroupExtended.doubleXDenominator'),
                  ('denominator_y','y.denominator',3,'GroupExtended.doubleYDenominator'))
    if addition:
        descriptions=(('numerator_x','x.numerator',0,'Group.cross'),
                      ('numerator_y','y.numerator',1,'Group.diagonal'),
                      ('denominator_x','x.denominator',2,f'fun left right : Group.Point F => 1 + Group.delta ({c}.coefficientD : F) left right'),
                      ('denominator_y','y.denominator',3,f'fun left right : Group.Point F => 1 - Group.delta ({c}.coefficientD : F) left right'))
    for export,target,i,formula in descriptions:
        cone=selected[i];role=cone['role'];output=f'{c}.{role}_{cone["output"]}'
        input_defs=','.join(f'{c}.{role}_{identity}' for identity in cone['inputs'])
        right_assignment = f'({m}.materialAssignment base)' if constructed_selector else 'base'
        arguments = f'(inputPoint base) (rightPoint {right_assignment})' if addition else '(inputPoint base)'
        field_preservation = ('''  have px := congrArg Group.Point.x preserved.1
  have py := congrArg Group.Point.y preserved.1
  have qx := congrArg Group.Point.x preserved.2
  have qy := congrArg Group.Point.y preserved.2
''' if addition and not constructed_selector else '''  have px := congrArg Group.Point.x preserved
  have py := congrArg Group.Point.y preserved
''')
        right_changes = (f'''  change eval ({m}.materialAssignment base) rightX = eval base rightX at qx
  change eval ({m}.materialAssignment base) rightY = eval base rightY at qy
''' if addition and not constructed_selector else '')
        normalizers = ('inputX,inputY,rightX,rightY' if addition else 'inputX,inputY')
        all_facts = 'px py qx qy' if addition and not constructed_selector else 'px py'
        rewrites = 'px,py,qx,qy' if addition and not constructed_selector else 'px,py'
        polynomials = (f'inputPoint,rightPoint,inputX,inputY,rightX,rightY,Group.cross,Group.diagonal,Group.delta,{c}.coefficientD' if addition else
            'inputPoint,inputX,inputY,GroupExtended.doubleNumerator,GroupExtended.doubleXDenominator,\n    GroupExtended.doubleYDenominator,Group.diagonal')
        source+=f'''theorem {export} {{F : Type}} [Field F] [CharP F modulus] (base : Nat → F)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    eval ({m}.materialAssignment base) {target} = ({formula}) {arguments} := by
  have value := {m}.{role}_constructed base one linked
  have identified : eval ({m}.materialAssignment base) {target} =
      eval ({m}.materialAssignment base) {output} :=
    Compiler.canonical_equal _ _ _ (by decide)
  rw [identified,value]
  have preserved := input_preserved base linked
{field_preservation}  change eval ({m}.materialAssignment base) inputX = eval base inputX at px
  change eval ({m}.materialAssignment base) inputY = eval base inputY at py
{right_changes}  simp only [{input_defs},{normalizers}] at {all_facts} ⊢
  rw [{rewrites}]
  simp only [{polynomials}] <;> ring
'''
    expected={index:term for stage in stages for index,term in zip(stage['rows'],lower_stage(stage)[1])}
    source+=f'''private theorem kept_separate : ∀ column ∈ {m}.kept, column ∉ x.writes ∧ column ∉ y.writes := by
  have checked : {m}.kept.all (fun column => decide (column ∉ x.writes ∧ column ∉ y.writes)) = true := by decide
  intro column member; exact of_decide_eq_true (List.all_eq_true.mp checked column member)
theorem protected_columns {{F : Type}} [Field F] [CharP F modulus] (base : Nat → F)
    (linked : base {copy} = base 0) : ∀ column ∈ {m}.kept, completed base column = base column := by
  intro column member
  exact (GroupQuotientPairCompletion.pair_preserves x y ({m}.materialAssignment base) column
    (kept_separate column member).1 (kept_separate column member).2).trans
    (({m}.material_rows_complete base linked).2 column member)
private theorem quotient_coverage : ∀ actual ∈ quotientRaw, ∃ expected ∈ GroupQuotientPairCompletion.rows x y,
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [quotientRaw,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in indices)+'\n'
    for index in indices:
        source+=f'''  · refine ⟨{expected[index]},?_,by decide,by decide⟩
    simp [GroupQuotientPairCompletion.rows,GroupQuotientPairCompletion.Coordinate.rows,x,y,
      GroupRowCompletion.quotientRows,ScalarCompletion.productRows,Compiler.subtract,scaleLinear]
'''
    right_input = (f'(rightPoint ({m}.materialAssignment base))' if constructed_selector else '(rightPoint base)') if addition else '(inputPoint base)'
    validity = (f'''(leftValid : Group.OnCurve ({c}.coefficientD : F) (inputPoint base))
    (rightValid : Group.OnCurve ({c}.coefficientD : F) {right_input})''' if addition else
        f'(valid : Group.OnCurve ({c}.coefficientD : F) (inputPoint base))')
    constructor = 'add_complete' if addition else 'double_complete'
    constructor_inputs = (f'(inputPoint base) {right_input} leftValid rightValid' if addition else
        '(inputPoint base) valid')
    closure = (f'''  have denominators := Group.denominators_nonzero ({c}.coefficientD : F) imaginary nonSquare imaginarySquare
    (inputPoint base) {right_input} leftValid rightValid
  have curved : Group.OnCurve ({c}.coefficientD : F)
      (Group.affineAdd ({c}.coefficientD : F) (inputPoint base) {right_input}) := by
    apply Group.affine_rows_onCurve ({c}.coefficientD : F) imaginary nonSquare imaginarySquare
      (inputPoint base) {right_input} _ leftValid rightValid
    · exact div_mul_cancel₀ _ denominators.1
    · exact div_mul_cancel₀ _ denominators.2
''' if addition else f'''  have curved := GroupExtended.optimized_double_sound ({c}.coefficientD : F) imaginary nonSquare imaginarySquare
    (inputPoint base) valid
''')
    closure_result = ('''  · rw [coordinates]
    exact curved
''' if addition else '''  · rw [coordinates,← curved.1]
    exact curved.2
''')
    source+=f'''theorem actual_point_complete {{F : Type}} [Field F] [CharP F modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({c}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (base : Nat → F)
    (one : base 0 = 1) (linked : base {copy} = base 0)
    {validity} :
    Satisfies (completed base) ({c}.rawRows ++ quotientRaw) ∧
      outputPoint (completed base) = Group.affineAdd ({c}.coefficientD : F) (inputPoint base) {right_input} ∧
      Group.OnCurve ({c}.coefficientD : F) (outputPoint (completed base)) := by
  have built := GroupQuotientPairCompletion.{constructor} ({c}.coefficientD : F) imaginary nonSquare imaginarySquare
    {constructor_inputs} x y ({m}.materialAssignment base) shapeX shapeY separate fresh (by decide)
    (numerator_x base one linked) (denominator_x base one linked)
    (numerator_y base one linked) (denominator_y base one linked)
  have material := {m}.material_rows_complete base linked
  have materialFresh : {c}.rawRows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (term.1 ∉ x.writes ∧ term.1 ∉ y.writes))) = true := by decide
  have earlier : Satisfies (completed base) {c}.rawRows := by
    intro row member
    have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval (completed base) terms = eval ({m}.materialAssignment base) terms := by
      apply eval_agrees; intro term present
      have outside := of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp materialFresh row member) term (inside term present))
      exact GroupQuotientPairCompletion.pair_preserves x y ({m}.materialAssignment base) term.1 outside.1 outside.2
    change Square (eval (completed base) row.a) (eval (completed base) row.b)
    rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
      agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
    exact material.1 row member
  have copyLink : completed base {copy} = completed base 0 := by
    rw [protected_columns base linked {copy} (by decide),protected_columns base linked 0 (by decide),linked]
  have quotient : Satisfies (completed base) quotientRaw := by
    intro actual member
    obtain ⟨expected,present,left,right⟩ := quotient_coverage actual member
    have result : Square (eval (completed base) expected.a) (eval (completed base) expected.b) := built.1 expected present
    rw [← Compiler.canonical_equal (completed base) _ _ left,
      ← Compiler.canonical_equal (completed base) _ _ right] at result
    simpa only [Compiler.eval_unoutline (completed base) {copy} _ copyLink] using result
{closure}  have coordinates : outputPoint (completed base) =
      Group.affineAdd ({c}.coefficientD : F) (inputPoint base) {right_input} := built.2
  refine ⟨?_,coordinates,?_⟩
  · intro row member
    rcases List.mem_append.mp member with first | second
    · exact earlier row first
    · exact quotient row second
{closure_result}'''
    for export in ('input_preserved',*(item[0] for item in descriptions),'protected_columns','actual_point_complete'):
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
