"""Selector equations from captured rows for one unchanged assignment."""
from . import transfer_ownership as owner
PREFIX = "RuntimeOwnershipWindow"
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_selector_completion as selector
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def render_selector(checked, plan, cones, window_offset, bits):
    # The neutral renderer checks all eight source/native operands, both cone
    # endpoints and the genuine six-formula select/add operation.
    original, _ = selector.render_selector(
        checked, plan, cones, window_offset, PREFIX, bits,
        native_inputs=True)
    stem = original[:-len('SelectorCompletion')]
    c = stem + 'Cones'
    name = stem + 'SelectorSoundness'
    group = next(g for g in plan['point_groups']
                 if g['index'] == 4 + 3 * window_offset)
    selected = [next(c for c in cones['cones']
                     if c['role'] == 'formula' + str(index))
                for index in (group['formula_start'] + 4,
                              group['formula_start'] + 5)]
    observe = lambda value: checked['derived'][value[1]] if value[0] == 'source' else completion.canonical([(0, value[1])])
    inputs = [*(observe(v) for role in ('base', 'twice', 'triple')
                for v in checked['points'][role]), *bits]
    output = tuple(map(observe, checked['windows'][window_offset][3]))
    roles = ('baseX', 'baseY', 'twiceX', 'twiceY', 'tripleX', 'tripleY', 'low', 'high')
    source = f'''import ShielddSecurity.{c}
import ShielddSecurity.GroupWindows
namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''
    for role, terms in zip(roles, inputs):
        source += f'def {role} : Linear := {linear(terms)}\n'
    for role in ('base', 'twice', 'triple'):
        source += f'''def {role}Point {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {role}X,eval rho {role}Y⟩
'''
    source += f'''def selected {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(output[0])},eval rho {linear(output[1])}⟩

theorem actual_selected {{F : Type}} [Field F] [CharP F {c}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {c}.rawRows) :
    selected rho = Group.windowPoint (eval rho low) (eval rho high)
      (basePoint rho) (twicePoint rho) (triplePoint rho) := by
  apply congrArg₂ Group.Point.mk
'''
    for axis, cone in enumerate(selected):
        role = cone['role']
        endpoint = f'{c}.{role}_{cone["output"]}'
        declarations = ','.join(f'{c}.{role}_{i}' for i in cone['inputs'])
        source += f'''  · have value := {c}.{role}_sound rho one satisfied
    have identified : eval rho {linear(output[axis])} = eval rho {endpoint} :=
      Compiler.canonical_equal _ _ _ (by decide)
    change eval rho {linear(output[axis])} = _
    rw [identified,value]
    simp only [{declarations},basePoint,twicePoint,triplePoint,{','.join(roles)},
      Group.windowPoint,Group.chooseCoordinate,eval]
    ring
'''
    source += f'''
theorem actual_curve {{F : Type}} [Field F] [CharP F {c}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {c}.rawRows)
    (lowBit highBit : Bool)
    (lowValue : eval rho low = if lowBit then 1 else 0)
    (highValue : eval rho high = if highBit then 1 else 0)
    (baseValid : Group.OnCurve ({c}.coefficientD : F) (basePoint rho))
    (twiceValid : Group.OnCurve ({c}.coefficientD : F) (twicePoint rho))
    (tripleValid : Group.OnCurve ({c}.coefficientD : F) (triplePoint rho)) :
    Group.OnCurve ({c}.coefficientD : F) (selected rho) := by
  rw [actual_selected rho one satisfied,lowValue,highValue]
  exact Group.window_onCurve ({c}.coefficientD : F) lowBit highBit
    (basePoint rho) (twicePoint rho) (triplePoint rho) baseValid twiceValid tripleValid
#print axioms actual_selected
#print axioms actual_curve
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)


def generate_window(checked, extracted, window_offset, readonly_lcs=()):
    owner.match_formulas(checked)
    plan = completion.window_plan(checked, extracted, window_offset, False, readonly_lcs)
    if plan['window_index'] == 0:
        raise relation.RelationError('folded first ownership selector needs its separate adapter')
    cones = owner.cone_certificates(checked, extracted, window_offset, False)
    observe = lambda value: checked['derived'][value[1]] if value[0] == 'source' else completion.canonical([(0, value[1])])
    bits = tuple(map(observe, checked['window_bits'][window_offset]))
    return render_selector(checked, plan, cones, window_offset, bits)
