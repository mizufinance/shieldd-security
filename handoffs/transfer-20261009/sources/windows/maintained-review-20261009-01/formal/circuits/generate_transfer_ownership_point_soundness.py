"""Arbitrary-assignment point soundness for retained ownership252 frames.

The neutral quotient/formula renderer rechecks actual local source plans. This
is separate from constructor correctness and from the full ownership/RNK loop.
"""
from . import generate_transfer_ownership_double_completion as point
from . import transfer_ownership_completion as completion, transfer_ownership as owner
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits

def render_point(checked, extracted, plan, cones, point_index):
    # This rechecks both actual quotient/formula endpoint associations and the
    # shared source LCs; a hash or a constructor conclusion is insufficient.
    original, _ = point.render_point(checked, extracted, plan, cones,
                                     point_index, 'RuntimeOwnershipWindow')
    group = next(g for g in plan['point_groups'] if g['index'] == point_index)
    addition = group['kind'] == 'add'
    first = group.get('formula_start', 4 * point_index)
    selected = [next(c for c in cones['cones'] if c['role'] == 'formula' + str(i))
                for i in range(first, first + 4)]
    stem = original[:-len('Completion')]
    c = stem + 'Cones'
    ns = stem + 'Soundness'
    copy = checked['metadata']['constant_copy']
    relation.natural(copy, 262144)
    source = f'''import ShielddSecurity.{original}
import ShielddSecurity.GroupQuotientRowSoundness
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def rawRows : List Row := {c}.rawRows ++ {original}.quotientRaw
def expectedRows : List Row := GroupQuotientPairCompletion.rows {original}.x {original}.y

theorem reverse_rows_checked : expectedRows.all (fun row =>
    Compiler.checkRow {original}.modulus (Compiler.unoutlineRows {copy} rawRows) row ||
    Compiler.checkRow {original}.modulus (Compiler.unoutlineRows {copy} rawRows)
      ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

theorem expected_rows_from_actual {{F : Type}} [Field F] [CharP F {original}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho expectedRows := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied (by decide)
  intro row member
  have checked := List.all_eq_true.mp reverse_rows_checked row member
  simp only [Bool.or_eq_true] at checked
  rcases checked with direct | reversed
  · exact Compiler.checked_row_sound rho _ row normalized direct
  · have truth := Compiler.checked_row_sound rho _
      ⟨scaleLinear (-1) row.a,row.b⟩ normalized reversed
    simpa only [eval_scale,Int.cast_neg,Int.cast_one,neg_one_mul,
      Square,neg_mul_neg] using truth
'''
    formulae = [
        ('numerator_x', 'x.numerator', 'GroupExtended.doubleNumerator'),
        ('numerator_y', 'y.numerator', 'fun p : Group.Point F => Group.diagonal p p'),
        ('denominator_x', 'x.denominator', 'GroupExtended.doubleXDenominator'),
        ('denominator_y', 'y.denominator', 'GroupExtended.doubleYDenominator'),
    ]
    if addition:
        formulae = [
            ('numerator_x', 'x.numerator', 'Group.cross'),
            ('numerator_y', 'y.numerator', 'Group.diagonal'),
            ('denominator_x', 'x.denominator', f'fun p q : Group.Point F => 1 + Group.delta ({c}.coefficientD : F) p q'),
            ('denominator_y', 'y.denominator', f'fun p q : Group.Point F => 1 - Group.delta ({c}.coefficientD : F) p q'),
        ]
    for cone, (export, target, formula) in zip(selected, formulae):
        role = cone['role']
        output = f'{c}.{role}_{cone["output"]}'
        inputs = ','.join(f'{c}.{role}_{identity}' for identity in cone['inputs'])
        arguments = f'({original}.inputPoint rho)'
        if addition:
            arguments += f' ({original}.rightPoint rho)'
        definitions = f'{original}.inputPoint,{original}.inputX,{original}.inputY'
        if addition:
            definitions += f',{original}.rightPoint,{original}.rightX,{original}.rightY'
        source += f'''
theorem {export} {{F : Type}} [Field F] [CharP F {original}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho {original}.{target} = ({formula}) {arguments} := by
  have cones : Satisfies rho {c}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have value := {c}.{role}_sound rho one cones
  have identified : eval rho {original}.{target} = eval rho {output} :=
    Compiler.canonical_equal _ _ _ (by decide)
  rw [identified,value]
  simp only [{inputs},{definitions},Group.cross,Group.diagonal,Group.delta,
    GroupExtended.doubleNumerator,GroupExtended.doubleXDenominator,
    GroupExtended.doubleYDenominator,{c}.coefficientD] <;> ring
'''
    d = f'({c}.coefficientD : F)'
    p = f'{original}.inputPoint rho'
    q = f'{original}.rightPoint rho' if addition else p
    validity = f'(leftValid : Group.OnCurve {d} ({p}))'
    if addition:
        validity += f'\n    (rightValid : Group.OnCurve {d} ({q}))'
    conclusion = f'{original}.outputPoint rho = Group.affineAdd {d} ({p}) ({q})'
    if not addition:
        conclusion += f' ∧ Group.OnCurve {d} ({original}.outputPoint rho)'
    source += f'''
/-- Every polynomial and quotient equation comes from this unchanged assignment.
Input curve membership is discharged by the preceding point/source joins. -/
theorem actual_point_sound {{F : Type}} [Field F] [CharP F {original}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare {d})
    (imaginarySquare : imaginary * imaginary = -1)
    {validity} (satisfied : Satisfies rho rawRows) :
    {conclusion} := by
  have expected := expected_rows_from_actual rho satisfied
  have xRows : Satisfies rho {original}.x.rows := by
    intro row member
    exact expected row (List.mem_append_left _ member)
  have yRows : Satisfies rho {original}.y.rows := by
    intro row member
    exact expected row (List.mem_append_right _ member)
  have xEquation := GroupQuotientRowSoundness.product_equation rho
    {original}.x.numerator {original}.x.denominator {original}.x.remainder
    {original}.x.output {original}.x.product {original}.x.auxiliary four xRows
  have yEquation := GroupQuotientRowSoundness.product_equation rho
    {original}.y.numerator {original}.y.denominator {original}.y.remainder
    {original}.y.output {original}.y.product {original}.y.auxiliary four yRows
  rw [numerator_x rho one satisfied,denominator_x rho one satisfied] at xEquation
  rw [numerator_y rho one satisfied,denominator_y rho one satisfied] at yEquation
'''
    if addition:
        source += f'''  exact Group.affine_rows_sound {d} imaginary nonSquare imaginarySquare
    ({p}) ({q}) ({original}.outputPoint rho) leftValid rightValid xEquation yEquation
'''
    else:
        source += f'''  apply Group.double_rows_sound {d} imaginary nonSquare imaginarySquare
    ({p}) ({original}.outputPoint rho) leftValid
  · exact xEquation
  · exact yEquation
'''
    exports = ['reverse_rows_checked', 'expected_rows_from_actual',
               'numerator_x', 'numerator_y', 'denominator_x', 'denominator_y',
               'actual_point_sound']
    source += ''.join(f'#print axioms {e}\n' for e in exports)
    source += f'end ShielddSecurity.{ns}\n'
    return ns, _signature_audits(source)


def generate_window(checked, extracted, window_offset, readonly_lcs=()):
    owner.match_formulas(checked)
    plan = completion.window_plan(checked, extracted, window_offset, False, readonly_lcs)
    cones = owner.cone_certificates(checked, extracted, window_offset, False)
    if plan['window_index'] == 0:
        raise relation.RelationError('folded first ownership window needs its separate soundness adapter')
    return [render_point(checked, extracted, plan, cones, group['index'])
            for group in plan['point_groups']]


def generate_precompute(checked, extracted, readonly_lcs=()):
    owner.match_formulas(checked)
    plan = completion.window_plan(checked, extracted, 0, True, readonly_lcs)
    cones = owner.cone_certificates(checked, extracted, 0, True)
    return [render_point(checked, extracted, plan, cones, index) for index in (0, 1)]
