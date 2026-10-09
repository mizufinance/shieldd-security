"""Join actual double/double/select/add rows on one arbitrary assignment."""
from . import transfer_ownership as owner
PREFIX = "RuntimeOwnershipWindow"
from . import generate_transfer_ownership_point_soundness as points
from . import generate_transfer_ownership_selector_soundness as selectors
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_window_curve_completion as window
from .generate_hash_round import _signature_audits


def generate_window(checked, extracted, window_offset, readonly_lcs=()):
    owner.match_formulas(checked)
    plan = completion.window_plan(checked, extracted, window_offset, False, readonly_lcs)
    # This validates operation order and all nonlinear coordinate outputs.
    original, _ = window.render_window(checked, plan, window_offset, PREFIX)
    cones = owner.cone_certificates(checked, extracted, window_offset, False)
    sound = [points.render_point(checked, extracted, plan, cones, g['index'])[0]
             for g in plan['point_groups']]
    selected, _ = selectors.generate_window(checked, extracted, window_offset, readonly_lcs)
    first, second, add = [m[:-len('Soundness')] + 'Completion' for m in sound]
    name = original[:-len('CurveCompletion')] + 'WindowSoundness'
    d = sound[0][:-len('Soundness')] + 'Cones.coefficientD'
    add_cones = sound[2][:-len('Soundness')] + 'Cones'
    source = ''.join(f'import ShielddSecurity.{m}\n' for m in [*sound, selected])
    source += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
def rawRows : List Row := ({sound[0]}.rawRows ++ {sound[1]}.rawRows) ++ {sound[2]}.rawRows

theorem second_input {{F : Type}} [Field F] (rho : Nat → F) :
    {second}.inputPoint rho = {first}.outputPoint rho := by
  simp only [{second}.inputPoint,{second}.inputX,{second}.inputY,{first}.outputPoint,
    GroupQuotientPairCompletion.point,{first}.x,{first}.y,eval,Int.cast_one,one_mul,add_zero]
theorem add_input {{F : Type}} [Field F] (rho : Nat → F) :
    {add}.inputPoint rho = {second}.outputPoint rho := by
  simp only [{add}.inputPoint,{add}.inputX,{add}.inputY,{second}.outputPoint,
    GroupQuotientPairCompletion.point,{second}.x,{second}.y,eval,Int.cast_one,one_mul,add_zero]
theorem selected_input {{F : Type}} [Field F] (rho : Nat → F) :
    {add}.rightPoint rho = {selected}.selected rho := rfl

theorem actual_window_sound {{F : Type}} [Field F] [CharP F {first}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({d} : F))
    (imaginarySquare : imaginary * imaginary = -1) (lowBit highBit : Bool)
    (incoming : Group.OnCurve ({d} : F) ({first}.inputPoint rho))
    (lowValue : eval rho {selected}.low = if lowBit then 1 else 0)
    (highValue : eval rho {selected}.high = if highBit then 1 else 0)
    (baseValid : Group.OnCurve ({d} : F) ({selected}.basePoint rho))
    (twiceValid : Group.OnCurve ({d} : F) ({selected}.twicePoint rho))
    (tripleValid : Group.OnCurve ({d} : F) ({selected}.triplePoint rho))
    (satisfied : Satisfies rho rawRows) :
    {add}.outputPoint rho = Group.affineAdd ({d} : F)
      (Group.affineAdd ({d} : F)
        (Group.affineAdd ({d} : F) ({first}.inputPoint rho) ({first}.inputPoint rho))
        (Group.affineAdd ({d} : F) ({first}.inputPoint rho) ({first}.inputPoint rho)))
      (Group.windowPoint (eval rho {selected}.low) (eval rho {selected}.high)
        ({selected}.basePoint rho) ({selected}.twicePoint rho) ({selected}.triplePoint rho)) := by
  have firstRows : Satisfies rho {sound[0]}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ (List.mem_append_left _ member))
  have secondRows : Satisfies rho {sound[1]}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ (List.mem_append_right _ member))
  have addRows : Satisfies rho {sound[2]}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  have selectorRows : Satisfies rho {add_cones}.rawRows := by
    intro row member
    exact addRows row (List.mem_append_left _ member)
  have firstResult := {sound[0]}.actual_point_sound rho one four imaginary nonSquare
    imaginarySquare incoming firstRows
  have secondIncoming : Group.OnCurve ({d} : F) ({second}.inputPoint rho) := by
    rw [second_input]; exact firstResult.2
  have secondResult := {sound[1]}.actual_point_sound rho one four imaginary nonSquare
    imaginarySquare secondIncoming secondRows
  have addIncoming : Group.OnCurve ({d} : F) ({add}.inputPoint rho) := by
    rw [add_input]; exact secondResult.2
  have rightValid : Group.OnCurve ({d} : F) ({add}.rightPoint rho) := by
    rw [selected_input]
    exact {selected}.actual_curve rho one selectorRows lowBit highBit lowValue highValue
      baseValid twiceValid tripleValid
  have result := {sound[2]}.actual_point_sound rho one four imaginary nonSquare
    imaginarySquare addIncoming rightValid addRows
  rw [add_input,secondResult.1,second_input,firstResult.1,selected_input,
    {selected}.actual_selected rho one selectorRows] at result
  exact result
#print axioms second_input
#print axioms add_input
#print axioms selected_input
#print axioms actual_window_sound
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
