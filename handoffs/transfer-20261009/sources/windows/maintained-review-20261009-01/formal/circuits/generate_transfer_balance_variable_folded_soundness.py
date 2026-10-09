"""Arbitrary row soundness for the genuine folded identity first window."""
from . import generate_transfer_balance_variable_completion as balance
from . import generate_transfer_balance_variable_selector_soundness as selectors
from . import transfer_balance_variable_completion as completion
from . import generate_transfer_ownership_folded_window_completion as folded
from . import generate_transfer_ownership_folded_window_curve as curve
from .generate_transfer_ownership_completion import lower_stage
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted, readonly_lcs=()):
    balance._checked(checked, 0)
    plan = completion.window_plan(checked, extracted, 0, False, readonly_lcs)
    cones = completion.cone_certificates(checked, extracted, 0, False)
    local, _ = folded.render_folded(checked, extracted, plan, balance.PREFIX)
    observe = lambda v: checked['derived'][v[1]] if v[0] == 'source' else completion.canonical([(0, v[1])])
    bits = tuple(map(observe, checked['window_bits'][0]))
    # Validate folded source operands and linear endpoints independently of the
    # arbitrary-assignment proof; there are no quotient stages on this path.
    curve.render_folded_curve(checked, plan, cones, local, bits, native_inputs=True)
    selector, selector_source = selectors.render_selector(checked, plan, cones, 0, bits)
    stages = plan['stages'][plan['point_groups'][2]['material_end']:plan['point_groups'][2]['stage_end']]
    c = selector[:-len('SelectorSoundness')] + 'Cones'
    name = balance.PREFIX + '000FoldedSoundness'
    raw = {r['row']: tuple(tuple((col, int(value, 16)) for col, value in r[key])
                          for key in ('a', 'b')) for r in extracted['selected_rows']}
    rows = ',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in plan['local_rows'])
    expected = [lower_stage(stage)[1][0] for stage in stages]
    copy = checked['metadata']['constant_copy']
    source = f'''import ShielddSecurity.{selector}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
def rawRows : List Row := [{rows}]
def expectedRows : List Row := [{','.join(expected)}]
def output {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨rho {stages[0]['output']},rho {stages[1]['output']}⟩

theorem selector_rows {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho rawRows) : Satisfies rho {c}.rawRows := by
  have checked : {c}.rawRows.all (fun row => decide (row ∈ rawRows)) = true := by decide
  intro row member
  exact satisfied row (of_decide_eq_true (List.all_eq_true.mp checked row member))

theorem reverse_rows_checked : expectedRows.all (fun row =>
    Compiler.checkRow {c}.modulus (Compiler.unoutlineRows {copy} rawRows) row ||
    Compiler.checkRow {c}.modulus (Compiler.unoutlineRows {copy} rawRows)
      ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

private theorem expected_rows {{F : Type}} [Field F] [CharP F {c}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho expectedRows := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied (by decide)
  intro row member
  have checked := List.all_eq_true.mp reverse_rows_checked row member
  simp only [Bool.or_eq_true] at checked
  rcases checked with direct | reversed
  · exact Compiler.checked_row_sound rho _ row normalized direct
  · have truth := Compiler.checked_row_sound rho _
      ⟨scaleLinear (-1) row.a,row.b⟩ normalized reversed
    simpa only [eval_scale,Int.cast_neg,Int.cast_one,neg_one_mul,Square,neg_mul_neg] using truth

theorem actual_output {{F : Type}} [Field F] [CharP F {c}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    output rho = {selector}.selected rho := by
  have rows := expected_rows rho satisfied
  apply congrArg₂ Group.Point.mk
'''
    for axis, row in enumerate(expected):
        member = 'List.mem_cons_self' if axis == 0 else '(List.mem_cons_of_mem _ (List.mem_singleton_self _))'
        source += f'''  · have truth := rows {row} {member}
    have zero := square_zero _ truth
    apply sub_eq_zero.mp
    simpa only [Compiler.eval_subtract,eval_append,eval,Int.cast_one,one_mul,add_zero] using zero
'''
    source += f'''
theorem actual_window_sound {{F : Type}} [Field F] [CharP F {c}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    output rho = Group.windowPoint (eval rho {selector}.low) (eval rho {selector}.high)
      ({selector}.basePoint rho) ({selector}.twicePoint rho) ({selector}.triplePoint rho) :=
  (actual_output rho satisfied).trans
    ({selector}.actual_selected rho one (selector_rows rho satisfied))
#print axioms selector_rows
#print axioms reverse_rows_checked
#print axioms actual_output
#print axioms actual_window_sound
end ShielddSecurity.{name}
'''
    return [(selector, selector_source), (name, _signature_audits(source))]
