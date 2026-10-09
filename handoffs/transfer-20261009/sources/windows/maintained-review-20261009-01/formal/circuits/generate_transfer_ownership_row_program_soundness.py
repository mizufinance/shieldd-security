"""Package actual ownership row windows for the arbitrary-assignment rule.

The empty stage lists express that these are row-soundness views only. No
constructor or witness-building result is claimed by these views.
"""
from . import transfer_ownership as owner
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_folded_soundness as folded
from . import generate_transfer_ownership_window_soundness as window
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted, readonly_lcs=()):
    owner.match_formulas(checked)
    first_plan = completion.window_plan(checked, extracted, 0, False, readonly_lcs)
    later_plan = completion.window_plan(checked, extracted, 1, False, readonly_lcs)
    assert (first_plan['window_index'], later_plan['window_index']) == (0, 1)
    folded.generate(checked, extracted, readonly_lcs)
    window.generate_window(checked, extracted, 1, readonly_lcs)
    observe = lambda value: checked['derived'][value[1]] if value[0] == 'source' else completion.canonical([(0, value[1])])
    coordinates = lambda pair: '(' + ','.join(linear(observe(value)) for value in pair) + ')'
    assert tuple(map(observe, checked['windows'][0][0])) == ((), ((0, 1),))
    name = 'RuntimeOwnershipRowPrograms'
    first = 'RuntimeOwnershipWindow000'
    later = 'RuntimeOwnershipWindow001'
    first_selector = first + 'Point4SelectorSoundness'
    later_selector = later + 'Point7SelectorSoundness'
    source = f'''import ShielddSecurity.{first}FoldedSoundness
import ShielddSecurity.{later}WindowSoundness
import ShielddSecurity.GroupVariableCircuitSoundness
set_option maxHeartbeats 250000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}

def firstTables : GroupVariableCircuitCompletion.Tables :=
  ⟨({first_selector}.baseX,{first_selector}.baseY),
    ({first_selector}.twiceX,{first_selector}.twiceY),
    ({first_selector}.tripleX,{first_selector}.tripleY)⟩
def laterTables : GroupVariableCircuitCompletion.Tables :=
  ⟨({later_selector}.baseX,{later_selector}.baseY),
    ({later_selector}.twiceX,{later_selector}.twiceY),
    ({later_selector}.tripleX,{later_selector}.tripleY)⟩

/-- Only the captured rows, coordinates and bits enter LocalSound. -/
def first (lowBit highBit : Bool) : GroupFixedCircuitCompletion.Program :=
  ⟨[],{first}FoldedSoundness.rawRows,
    {coordinates(checked['windows'][0][0])},{coordinates(checked['windows'][0][4])},
    {first_selector}.low,{first_selector}.high,lowBit,highBit⟩
def later (lowBit highBit : Bool) : GroupFixedCircuitCompletion.Program :=
  ⟨[],{later}WindowSoundness.rawRows,
    {coordinates(checked['windows'][1][0])},{coordinates(checked['windows'][1][4])},
    {later_selector}.low,{later_selector}.high,lowBit,highBit⟩

theorem tables_same : firstTables = laterTables := by rfl

theorem first_input_identity {{F : Type}} [Field F] (rho : Nat → F)
    (one : rho 0 = 1) (lowBit highBit : Bool) :
    GroupFixedCircuitCompletion.point rho (first lowBit highBit).input = Group.identityPoint := by
  simp only [first,GroupFixedCircuitCompletion.point,Group.identityPoint,
    eval,Int.cast_one,one_mul,add_zero,one]

theorem first_sound {{F : Type}} [Field F] [CharP F {first}Point4Cones.modulus]
    (lowBit highBit : Bool) :
    GroupVariableCircuitSoundness.LocalSound ({first}Point4Cones.coefficientD : F)
      {checked['metadata']['constant_copy']} firstTables (first lowBit highBit) := by
  intro rho one linked incoming curved low high satisfied
  change Satisfies rho {first}FoldedSoundness.rawRows at satisfied
  have result := {first}FoldedSoundness.actual_window_sound rho one satisfied
  rw [first_input_identity rho one,GroupVariableCircuitNative.affine_identity_left,
    GroupVariableCircuitNative.affine_identity_left,GroupVariableCircuitNative.affine_identity_left]
  simpa only [first,firstTables,GroupFixedCircuitCompletion.point,
    {first}FoldedSoundness.output,{first_selector}.basePoint,{first_selector}.twicePoint,
    {first_selector}.triplePoint,eval,Int.cast_one,one_mul,add_zero] using result

theorem later_sound {{F : Type}} [Field F] [CharP F {later}Point5Completion.modulus]
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({later}Point5Cones.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitSoundness.LocalSound ({later}Point5Cones.coefficientD : F)
      {checked['metadata']['constant_copy']} laterTables (later lowBit highBit) := by
  intro rho one linked incoming curved low high satisfied
  change Satisfies rho {later}WindowSoundness.rawRows at satisfied
  have result := {later}WindowSoundness.actual_window_sound rho one four imaginary
    nonSquare imaginarySquare lowBit highBit incoming low high curved.1 curved.2.1 curved.2.2 satisfied
  simpa only [later,laterTables,GroupFixedCircuitCompletion.point,
    {later}Point5Completion.inputPoint,{later}Point5Completion.inputX,{later}Point5Completion.inputY,
    {later}Point7Completion.outputPoint,GroupQuotientPairCompletion.point,
    {later}Point7Completion.x,{later}Point7Completion.y,
    {later_selector}.basePoint,{later_selector}.twicePoint,{later_selector}.triplePoint,
    eval,Int.cast_one,one_mul,add_zero] using result
'''
    for export in ['tables_same', 'first_input_identity', 'first_sound', 'later_sound']:
        source += f'#print axioms {export}\n'
    return name, _signature_audits(source + f'end ShielddSecurity.{name}\n')
