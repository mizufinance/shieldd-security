"""Construct a later variable-window selector from its exact owned rows.

The source certificates and materialization constructor fix the actual eight
operands. Boolean meanings and table curve facts are independent inputs to the
local curve theorem; the whole owned loop must derive and preserve them.
"""
from . import transfer_ownership_completion as completion
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted, window_offset, readonly_lcs=()):
    if type(window_offset) is not int or not 0 <= window_offset < len(checked['windows']):
        raise completion.relation.RelationError('ownership typed bounded selector selection')
    plan = completion.window_plan(checked, extracted, window_offset, False, readonly_lcs)
    cones = completion.owner.cone_certificates(checked, extracted, window_offset, False)
    prefix = 'RuntimeRnkWindow' if checked['metadata'].get('schema') == 'shieldd-transfer-rnk-dh-v1' else 'RuntimeOwnershipWindow'
    low_index = 2*(125-plan['window_index'])
    bits = tuple(checked['derived'][handle] for handle in checked['bits'][low_index:low_index+2])
    return render_selector(checked,plan,cones,window_offset,prefix,bits)


def render_selector(checked,plan,cones,window_offset,prefix,bits,*,native_inputs=False):
    """Neutral selector with exact ingress-derived source/native bit LCs."""
    import re
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',prefix) is None or len(bits)!=2:
        raise completion.relation.RelationError('selector namespace/bit pair')
    point_index = 4 + 3*window_offset
    matches = [group for group in plan['point_groups'] if group['index'] == point_index]
    if len(matches) != 1 or matches[0]['kind'] != 'add' or matches[0]['formula_count'] != 6:
        raise completion.relation.RelationError('ownership exact select/add six formula group')
    first = matches[0]['formula_start']
    selected = [next(cone for cone in cones['cones'] if cone['role'] == 'formula'+str(index))
                for index in (first+4, first+5)]
    observe = lambda value: checked['derived'][value[1]] if value[0] == 'source' else completion.canonical([(0,value[1])])
    points = {role: tuple(map(observe, checked['points'][role])) for role in ('base','twice','triple')}
    low, high = bits
    inputs = [*points['base'], *points['twice'], *points['triple'], low, high]
    expected_inputs=inputs
    if native_inputs:
        observed=[*checked['points']['base'],*checked['points']['twice'],*checked['points']['triple'],
                  *checked['window_bits'][window_offset]]
        expected_inputs=[terms for role,terms in zip(observed,inputs) if role[0]=='source']
    if any([cones['observations'][identity][1] for identity in cone['inputs']] != expected_inputs for cone in selected):
        raise completion.relation.RelationError('ownership selector exact eight shared source roles')
    selector = tuple(map(observe, checked['windows'][window_offset][3]))
    if any(cones['observations'][cone['output']][1] != selector[axis]
           for axis, cone in enumerate(selected)):
        raise completion.relation.RelationError('ownership selector exact observed coordinate endpoints')
    stem = prefix+f'{plan["window_index"]:03d}Point{point_index}'
    c = stem+'Cones'; m = stem+'Materializations'; name = stem+'SelectorCompletion'
    copy = checked['metadata']['constant_copy']; roles = ('baseX','baseY','twiceX','twiceY','tripleX','tripleY','low','high')
    source = f'''import ShielddSecurity.{m}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
'''
    for role, terms in zip(roles, inputs):
        source += f'def {role} : Linear := {linear(terms)}\n'
    for role in ('base','twice','triple'):
        source += f'''def {role}Point {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {role}X,eval rho {role}Y⟩
'''
    source += f'''def selected {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(selector[0])},eval rho {linear(selector[1])}⟩
private theorem eval_kept {{F : Type}} [Field F] [CharP F {m}.modulus]
    (base : Nat → F) (linked : base {copy} = base 0) (terms : Linear)
    (inside : ∀ term ∈ terms, term.1 ∈ {m}.kept) :
    eval ({m}.materialAssignment base) terms = eval base terms := by
  apply eval_agrees; intro term member
  exact ({m}.material_rows_complete base linked).2 term.1 (inside term member)
theorem material_selected {{F : Type}} [Field F] [CharP F {m}.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = base 0) :
    selected ({m}.materialAssignment base) = Group.windowPoint (eval base low) (eval base high)
      (basePoint base) (twicePoint base) (triplePoint base) := by
  apply congrArg₂ Group.Point.mk
'''
    for axis, cone in enumerate(selected):
        role = cone['role']; output = c+'.'+role+'_'+cone['output']
        source += f'''  · have value := {m}.{role}_constructed base one linked
    have identified : eval ({m}.materialAssignment base) {linear(selector[axis])} =
        eval ({m}.materialAssignment base) {output} := Compiler.canonical_equal _ _ _ (by decide)
    change eval ({m}.materialAssignment base) {linear(selector[axis])} = _
    rw [identified,value]
'''
        preserved_inputs = [f'eval_kept base linked {c}.{role}_{identity} (by decide)'
                            for identity in cone['inputs']]
        source += '    simp only ['+','.join(preserved_inputs)+']\n'
        declarations = ','.join(c+'.'+role+'_'+identity for identity in cone['inputs'])
        source += f'''    simp only [{declarations},basePoint,twicePoint,triplePoint,{','.join(roles)},
      Group.windowPoint,Group.chooseCoordinate{',eval' if native_inputs else ''}]
    ring
'''
    source += f'''theorem material_curve {{F : Type}} [Field F] [CharP F {m}.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = base 0) (lowBit highBit : Bool)
    (lowValue : eval base low = if lowBit then 1 else 0)
    (highValue : eval base high = if highBit then 1 else 0)
    (baseValid : Group.OnCurve ({c}.coefficientD : F) (basePoint base))
    (twiceValid : Group.OnCurve ({c}.coefficientD : F) (twicePoint base))
    (tripleValid : Group.OnCurve ({c}.coefficientD : F) (triplePoint base)) :
    Group.OnCurve ({c}.coefficientD : F) (selected ({m}.materialAssignment base)) := by
  rw [material_selected base one linked,lowValue,highValue]
  exact Group.window_onCurve ({c}.coefficientD : F) lowBit highBit
    (basePoint base) (twicePoint base) (triplePoint base) baseValid twiceValid tripleValid
#print axioms material_selected
#print axioms material_curve
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
