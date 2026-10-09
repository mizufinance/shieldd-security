"""Construct the exact signed final addition from an independently replayed plan.

This emits no runtime certificate on its own. Genuine variable5/blinding8/
caller role association and the original-row replay belong to the strict
ingress. Prior unsigned/blinding curve facts are outputs of those preceding
constructors; the sign, arithmetic products, denominator legality and both
quotients are derived here. Native endpoint and whole Transfer joins remain
separate until their actual parents exist.
"""
import re
from . import transfer_balance_final_add as final, transfer_relation as relation
from .transfer_balance_rows import canonical, combine
from .generate_transfer_ownership_completion import lower_stage
from .generate_hash_round import linear, signed, _signature_audits


def generate_from_joint(variable_parent, variable_pages, blinding_parent, blinding_pages,
                        caller_parent, caller_page, accepted_roles, signed_value,
                        asset_base, blinding_base, joint, *,
                        namespace='RuntimeTransferBalanceFinalAddCompletion'):
    """Reaccept genuine parents and use the ONE retained joint original replay.

    The root's replay receipt and immutable extraction remain mandatory. This
    function does not reopen an ordinary stream or promote packet flags. It
    checks the exact parent/source-LC views before the neutral row renderer.
    """
    source = final.from_ingress(variable_parent, variable_pages, blinding_parent, blinding_pages,
                               caller_parent, caller_page, accepted_roles, signed_value,
                               asset_base, blinding_base)
    if (not isinstance(joint, dict) or type(joint.get('ordinary_replays')) is not int or joint['ordinary_replays'] != 1 or
            joint.get('parents') != source or not isinstance(joint.get('final_add'), dict) or
            joint['final_add'].get('roles') != source['roles'] or
            joint['final_add'].get('identity') != joint.get('identity')):
        raise relation.RelationError('final addition exact retained joint replay/source parents')
    return render_plan(joint['final_add'], namespace=namespace)


def _recheck(plan):
    """Reconstruct every owned row/stage from retained physical row data."""
    if isinstance(plan, dict) and plan.get('lowering') == 'point_shared_inverse':
        from .generate_transfer_balance_shared_add_completion import _recheck as shared_recheck
        return shared_recheck(plan)
    if not isinstance(plan, dict) or not isinstance(plan.get('protected'), list):
        raise relation.RelationError('final addition retained plan required')
    protected = plan['protected']
    if len(protected) > 4096 or protected != sorted(set(protected)):
        raise relation.RelationError('final addition bounded exact protected columns')
    for column in protected:
        relation.natural(column, 262144)
    matcher = final.Matcher(plan.get('roles'))
    rows = plan.get('selected_rows')
    if not isinstance(rows, list) or not 1 <= len(rows) <= 256:
        raise relation.RelationError('final addition bounded actual selected rows')
    for row in rows:
        matcher.observe(row)
    checked = matcher.finish(plan.get('identity', {}), tuple(((c, 1),) for c in protected))
    for key in ('parents', 'roles', 'signed', 'numerator', 'denominator', 'stages',
                'writes', 'protected', 'selected_rows'):
        if checked[key] != plan.get(key):
            raise relation.RelationError('final addition retained plan changed: ' + key)
    quotients = [stage for stage in checked['stages'] if stage['kind'] == 'quotient']
    if (len(quotients) != 2 or [stage['role'] for stage in quotients] != ['quotient.0', 'quotient.1'] or
            tuple(((stage['quotient'], 1),) for stage in quotients) != checked['roles']['output']):
        raise relation.RelationError('final addition original output coordinate pivots')
    return checked, matcher


def render_plan(plan, *, namespace='RuntimeTransferBalanceFinalAddCompletion'):
    """Neutral checked-plan renderer, never a qualification or ordinary replay.

    All theorem statements and every original-row certificate are audited.
    Unsupported lowered shapes refuse in _recheck rather than becoming an
    assumed legal quotient or a guessed native endpoint.
    """
    if isinstance(plan, dict) and plan.get('lowering') == 'point_shared_inverse':
        from .generate_transfer_balance_shared_add_completion import render_plan as shared_render
        return shared_render(plan, namespace=namespace)
    if not isinstance(namespace, str) or re.fullmatch('[A-Za-z][A-Za-z0-9_]*', namespace) is None:
        raise relation.RelationError('final addition Lean namespace')
    checked, matcher = _recheck(plan)
    stages = checked['stages']
    products = [stage for stage in stages if stage['kind'] == 'product']
    quotients = [stage for stage in stages if stage['kind'] == 'quotient']
    lowered = [lower_stage(stage) for stage in products]
    material_terms = [term for term, _ in lowered] + ['.compiler (.equal [] [])']
    quotient_terms = [lower_stage(stage)[0] for stage in quotients]
    writes = [column for stage in stages for column in
              ([stage['output'], stage['auxiliary']] if stage['kind'] == 'product' else
               [stage['quotient'], stage['product'], stage['auxiliary']])]
    if sorted(writes) != checked['writes']:
        raise relation.RelationError('final addition exact ordered write footprint')
    expected = {index: row for stage, (_, rows) in zip(products, lowered)
                for index, row in zip(stage['rows'], rows)}
    for stage in quotients:
        expected.update(zip(stage['rows'], lower_stage(stage)[1]))
    constant = (canonical([(0, 1), (200692, -1)]), ())
    raw = {record['row']: tuple(tuple((c, int(v, 16)) for c, v in record[key])
                               for key in ('a', 'b')) for record in checked['selected_rows']}
    links = [index for index, row in raw.items() if row == constant]
    if len(links) != 1:
        raise relation.RelationError('final addition unique actual copied constant')
    expected[links[0]] = '⟨[],[]⟩'
    if set(expected) != set(raw):
        raise relation.RelationError('final addition every retained original row coverage')

    def coordinate(stage):
        return '⟨' + ','.join([linear(stage[k]) for k in ('numerator', 'denominator', 'remainder')] +
                              [str(stage[k]) for k in ('quotient', 'product', 'auxiliary')]) + '⟩'

    source = f'''import ShielddSecurity.GroupQuotientPairCompletion
import ShielddSecurity.GroupCircuitSequenceCompletion
import ShielddSecurity.GroupSignedPoint
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{namespace}
-- Retained original-row construction; native variable65/H/SDK association is
-- still a separate preceding-constructor join. No honest row truth is assumed.
def modulus : Nat := {relation.MODULUS}
def d : Int := {signed(final.D)}
def kept : List Nat := {checked['protected']}
def ownedWrites : List Nat := {writes}
def materialSteps : List GroupCircuitCompletion.Step := [{','.join(material_terms)}]
def x : GroupQuotientPairCompletion.Coordinate := {coordinate(quotients[0])}
def y : GroupQuotientPairCompletion.Coordinate := {coordinate(quotients[1])}
def quotientSteps : List GroupCircuitCompletion.Step := [{','.join(quotient_terms)}]
def steps : List GroupCircuitCompletion.Step := materialSteps ++ quotientSteps
def expectedRows : List Row := GroupCircuitCompletion.emitted materialSteps ++ GroupQuotientPairCompletion.rows x y
def originalIndices : List Nat := {sorted(raw)}
def rawRows : List Row := [{','.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(raw))}]
def negative : Linear := {linear(checked['roles']['negative'])}
def unsignedX : Linear := {linear(checked['roles']['unsigned'][0])}
def unsignedY : Linear := {linear(checked['roles']['unsigned'][1])}
def blindedX : Linear := {linear(checked['roles']['blinded'][0])}
def blindedY : Linear := {linear(checked['roles']['blinded'][1])}
def signedX : Linear := {linear(checked['signed'][0])}
def signedY : Linear := {linear(checked['signed'][1])}
def unsignedPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho unsignedX,eval rho unsignedY⟩
def blindedPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho blindedX,eval rho blindedY⟩
def signedPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho signedX,eval rho signedY⟩
def materialAssignment {{F : Type}} [Field F] (base : Nat → F) : Nat → F := GroupCircuitCompletion.run base materialSteps
def completeAssignment {{F : Type}} [Field F] (base : Nat → F) : Nat → F :=
  GroupQuotientPairCompletion.build x y (materialAssignment base)
def outputPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := GroupQuotientPairCompletion.point x y rho
theorem ordered : GroupCircuitCompletion.Topological kept [] materialSteps :=
  GroupCircuitOrder.checked_order kept [] materialSteps (by decide)
private theorem material_legal {{F : Type}} [Field F] (base : Nat → F) :
    GroupCircuitCompletion.Legal base materialSteps := by
  simp [materialSteps,GroupCircuitCompletion.Legal,GroupCircuitCompletion.Step.Legal,
    CompilerCompletion.Step.Legal,eval]
theorem material_rows {{F : Type}} [Field F] (base : Nat → F) :
    Satisfies (materialAssignment base) (GroupCircuitCompletion.emitted materialSteps) :=
  GroupCircuitCompletion.run_constructs base materialSteps kept ordered (material_legal base)
theorem material_preserves {{F : Type}} [Field F] (base : Nat → F) (terms : Linear)
    (included : ∀ term ∈ terms, term.1 ∈ kept) :
    eval (materialAssignment base) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact GroupCircuitCompletion.run_preserves base materialSteps kept [] ordered term.1 (included term member)
theorem factor {{F : Type}} [Field F] (base : Nat → F) :
    GroupCircuitCompletion.run base steps = completeAssignment base := by
  rw [steps,GroupCircuitSequenceCompletion.run_append]
  rfl
theorem writes_exact : GroupCircuitSequenceCompletion.writes steps = ownedWrites := by
  decide
theorem outside {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (excluded : column ∉ ownedWrites) : completeAssignment base column = base column := by
  rw [← factor]
  exact GroupCircuitSequenceCompletion.run_preserves base steps column (by rw [writes_exact]; exact excluded)
theorem outside_eval {{F : Type}} [Field F] (base : Nat → F) (terms : Linear)
    (excluded : ∀ term ∈ terms, term.1 ∉ ownedWrites) :
    eval (completeAssignment base) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact outside base term.1 (excluded term member)
theorem preserves_earlier_rows {{F : Type}} [Field F] (base : Nat → F) (prior : List Row)
    (constructed : Satisfies base prior)
    (excluded : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ ownedWrites) :
    Satisfies (completeAssignment base) prior := by
  rw [← factor]
  apply GroupCircuitSequenceCompletion.preserves_rows base steps prior constructed
  intro row member term present
  rw [writes_exact]
  exact excluded row member term present
private theorem four_nonzero {{F : Type}} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
'''
    for role in ('sign', 'xx', 'yy', 'sum', 'xy'):
        left, right = matcher.requests[role]
        output = matcher.products[role]['output']
        for label, terms in (('Left', left), ('Right', right), ('Output', output)):
            source += f'def {role}{label} : Linear := {linear(terms)}\n'
        source += f'''theorem {role}_product {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) :
    eval (materialAssignment base) {role}Output =
      eval (materialAssignment base) {role}Left * eval (materialAssignment base) {role}Right := by
'''
        stage = next((stage for stage in products if stage['role'] == role), None)
        if stage:
            source += f'''  have calculated := Compiler.checked_product_sound (materialAssignment base)
    (GroupCircuitCompletion.emitted materialSteps) {linear(stage['left'])} {linear(stage['right'])}
    ({linear(output)}) [({stage['auxiliary']},1)] (four_nonzero (F := F)) (material_rows base)
    (by decide) (by decide)
  simpa only [{role}Output,{role}Left,{role}Right,mul_comm] using calculated
'''
        else:
            folded = next(((scalar, other) for scalar, other in ((left, right), (right, left))
                           if not scalar or len(scalar) == 1 and scalar[0][0] == 0), None)
            if folded is None:
                raise relation.RelationError('final addition unsupported material product')
            scalar, other = folded
            coefficient = signed(scalar[0][1]) if scalar else 0
            source += f'''  have materialOne : materialAssignment base 0 = 1 :=
    (GroupCircuitCompletion.run_preserves base materialSteps kept [] ordered 0 (by decide)).trans one
  have identified := Compiler.canonical_equal (materialAssignment base) {role}Output
    (scaleLinear {coefficient} {linear(other)}) (by decide)
  rw [identified,eval_scale]
  simp only [{role}Left,{role}Right,eval,materialOne,mul_one,add_zero,zero_mul,mul_zero]
  ring
'''

    source += '''theorem material_signed {F : Type} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (sign : Bool)
    (signValue : eval base negative = if sign then 1 else 0) :
    signedPoint (materialAssignment base) = GroupSignedPoint.signed sign (unsignedPoint base) := by
  have calculated := sign_product base one
  have signedValue := Compiler.canonical_equal (materialAssignment base) signedX (unsignedX ++ signOutput) (by decide)
  have signLeftValue := Compiler.canonical_equal (materialAssignment base) signLeft negative (by decide)
  have signRightValue := Compiler.canonical_equal (materialAssignment base) signRight (scaleLinear (-2) unsignedX) (by decide)
  rw [signLeftValue,signRightValue,eval_scale,
    material_preserves base negative (by decide),material_preserves base unsignedX (by decide),signValue] at calculated
  apply congrArg₂ Group.Point.mk
  · change eval (materialAssignment base) signedX = _
    rw [signedValue,eval_append,material_preserves base unsignedX (by decide),calculated]
    simp only [GroupSignedPoint.signed,unsignedPoint,Int.cast_neg,Int.cast_ofNat]
    ring
  · change eval (materialAssignment base) signedY = eval base unsignedY
    have identified := Compiler.canonical_equal (materialAssignment base) signedY unsignedY (by decide)
    rw [identified]
    exact material_preserves base unsignedY (by decide)
private theorem blinded_preserved {F : Type} [Field F] (base : Nat → F) :
    blindedPoint (materialAssignment base) = blindedPoint base :=
  congrArg₂ Group.Point.mk (material_preserves base blindedX (by decide))
    (material_preserves base blindedY (by decide))
'''
    # Derive source polynomial meanings from the calculated product rows. Each
    # alias equality below is a finite canonical LC certificate, not an input.
    statements = [('numerator_x', 'x.numerator', 'Group.cross', 'Compiler.subtract sumOutput (xxOutput ++ yyOutput)',
                   ('sum', 'xx', 'yy')),
                  ('numerator_y', 'y.numerator', 'Group.diagonal', 'yyOutput ++ xxOutput', ('yy', 'xx')),
                  ('denominator_x', 'x.denominator', 'fun a b : Group.Point F => 1 + Group.delta (d : F) a b',
                   '[(0,1)] ++ scaleLinear d xyOutput', ('xy', 'xx', 'yy')),
                  ('denominator_y', 'y.denominator', 'fun a b : Group.Point F => 1 - Group.delta (d : F) a b',
                   'Compiler.subtract [(0,1)] (scaleLinear d xyOutput)', ('xy', 'xx', 'yy'))]
    role_equalities = [('xxLeft', 'signedX'), ('xxRight', 'blindedX'),
                       ('yyLeft', 'signedY'), ('yyRight', 'blindedY'),
                       ('sumLeft', 'signedX ++ signedY'), ('sumRight', 'blindedX ++ blindedY'),
                       ('xyLeft', 'xxOutput'), ('xyRight', 'yyOutput')]
    for export, target, formula, expression, used in statements:
        source += f'''theorem {export} {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) :
    eval (materialAssignment base) {target} = ({formula})
      (signedPoint (materialAssignment base)) (blindedPoint base) := by
  have identified := Compiler.canonical_equal (materialAssignment base) {target} ({expression}) (by decide)
  rw [identified]
'''
        for role in used:
            source += f'  have {role}Value := {role}_product base one\n'
        for label, expression in role_equalities:
            source += f'  have {label}Same := Compiler.canonical_equal (materialAssignment base) {label} ({expression}) (by decide)\n'
        source += '''  have materialOne : materialAssignment base 0 = 1 :=
    (GroupCircuitCompletion.run_preserves base materialSteps kept [] ordered 0 (by decide)).trans one
  simp only [xxLeftSame,xxRightSame,yyLeftSame,yyRightSame,sumLeftSame,sumRightSame,
    xyLeftSame,xyRightSame,eval_append] at *
  have unit : eval (materialAssignment base) [(0,1)] = 1 := by
    simp only [eval,Int.cast_one,one_mul,add_zero,materialOne]
  simp only [Compiler.eval_subtract,eval_append,eval_scale,'''+','.join(role+'Value' for role in used)+''',unit]
  simp only [material_preserves base blindedX (by decide),material_preserves base blindedY (by decide)]
  simp only [signedPoint,blindedPoint,Group.cross,Group.diagonal,Group.delta]
  ring
'''

    source += '''private theorem shapeX : x.Shape := by
  simp [x,GroupQuotientPairCompletion.Coordinate.Shape,GroupQuotientPairCompletion.Coordinate.inputs,
    GroupQuotientPairCompletion.Coordinate.writes,GroupRowCompletion.writes]
private theorem shapeY : y.Shape := by
  simp [y,GroupQuotientPairCompletion.Coordinate.Shape,GroupQuotientPairCompletion.Coordinate.inputs,
    GroupQuotientPairCompletion.Coordinate.writes,GroupRowCompletion.writes]
private theorem separate : ∀ term ∈ y.inputs, term.1 ∉ x.writes := by
  have checked : y.inputs.all (fun term => decide (term.1 ∉ x.writes)) = true := by decide
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)
private theorem fresh : ∀ row ∈ x.rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ y.writes := by
  have checked : x.rows.all (fun row => (row.a ++ row.b).all (fun term => decide (term.1 ∉ y.writes))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
theorem original_coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    Compiler.canonical modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ''' + ' | '.join('rfl' for _ in sorted(raw)) + '\n'
    for index in sorted(raw):
        source += f'''  · refine ⟨{expected[index]},?_,by decide,by decide⟩
    simp [expectedRows,materialSteps,GroupCircuitCompletion.emitted,GroupCircuitCompletion.Step.rows,
      CompilerCompletion.Step.rows,ScalarCompletion.productRows,GroupQuotientPairCompletion.rows,
      GroupQuotientPairCompletion.Coordinate.rows,x,y,GroupRowCompletion.quotientRows,
      Compiler.subtract,scaleLinear]
'''
    source += '''theorem actual_rows_complete {F : Type} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base 200692 = base 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (sign : Bool) (signValue : eval base negative = if sign then 1 else 0)
    (unsignedCurved : Group.OnCurve (d : F) (unsignedPoint base))
    (blindingCurved : Group.OnCurve (d : F) (blindedPoint base)) :
    Satisfies (completeAssignment base) rawRows ∧
      outputPoint (completeAssignment base) = Group.affineAdd (d : F)
        (GroupSignedPoint.signed sign (unsignedPoint base)) (blindedPoint base) := by
  have signedCoordinates := material_signed base one sign signValue
  have signedCurved : Group.OnCurve (d : F) (signedPoint (materialAssignment base)) := by
    rw [signedCoordinates]
    exact GroupSignedPoint.signed_on_curve (d : F) sign (unsignedPoint base) unsignedCurved
  have built := GroupQuotientPairCompletion.add_complete (d : F) imaginary nonSquare imaginarySquare
    (signedPoint (materialAssignment base)) (blindedPoint base) signedCurved blindingCurved
    x y (materialAssignment base) shapeX shapeY separate fresh (by decide)
    (numerator_x base one) (denominator_x base one) (numerator_y base one) (denominator_y base one)
  have priorFresh : (GroupCircuitCompletion.emitted materialSteps).all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ x.writes ∧ term.1 ∉ y.writes))) = true := by decide
  have retained : Satisfies (completeAssignment base) (GroupCircuitCompletion.emitted materialSteps) := by
    intro row member
    have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval (completeAssignment base) terms = eval (materialAssignment base) terms := by
      apply eval_agrees
      intro term present
      have excluded := of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp priorFresh row member) term (inside term present))
      exact GroupQuotientPairCompletion.pair_preserves x y (materialAssignment base) term.1 excluded.1 excluded.2
    rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
      agrees row.b (by intro term present; exact List.mem_append_right _ present)]
    exact material_rows base row member
  have expected : Satisfies (completeAssignment base) expectedRows := by
    intro row member
    rcases List.mem_append.mp member with old | current
    · exact retained row old
    · exact built.1 row current
  have copyLink : completeAssignment base 200692 = completeAssignment base 0 := by
    rw [outside base 200692 (by decide),outside base 0 (by decide),linked]
  constructor
  · intro actual member
    obtain ⟨row,present,left,right⟩ := original_coverage actual member
    have truth : Square (eval (completeAssignment base) row.a) (eval (completeAssignment base) row.b) := expected row present
    rw [← Compiler.canonical_equal (completeAssignment base) _ _ left,
      ← Compiler.canonical_equal (completeAssignment base) _ _ right] at truth
    simpa only [Compiler.eval_unoutline (completeAssignment base) 200692 _ copyLink] using truth
  · exact built.2.trans (congrArg (fun point => Group.affineAdd (d : F) point (blindedPoint base)) signedCoordinates)
'''
    exports = ('ordered', 'material_rows', 'material_preserves', 'factor', 'writes_exact',
               'outside', 'outside_eval', 'preserves_earlier_rows',
               *(role+'_product' for role in ('sign', 'xx', 'yy', 'sum', 'xy')),
               'material_signed', *(item[0] for item in statements), 'original_coverage', 'actual_rows_complete')
    for export in exports:
        source += '#print axioms '+export+'\n'
    return namespace, _signature_audits(source+f'end ShielddSecurity.{namespace}\n')
