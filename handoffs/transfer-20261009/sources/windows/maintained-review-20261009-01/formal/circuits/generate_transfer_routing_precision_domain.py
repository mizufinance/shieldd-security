"""Join all33 physical zero tests with the separate onehot assertion.

The precision bound is a conclusion about arbitrary satisfying assignments.
No desired selector equations or prior precision bound is a premise.
"""
from .generate_transfer_routing_zero_rows import _lc, _row


def _member(position):
    result = 'List.mem_cons.mpr (Or.inl rfl)'
    for _ in range(position):
        result = 'List.mem_cons.mpr (Or.inr (' + result + '))'
    return result


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-row-derivative-v1'
    raw = {row['row']: row for row in extraction['selected_rows']}
    result = {}
    for slot, precision in enumerate(extraction['plan']['precision']):
        assert [s['value'] for s in precision['steps']] == list(range(33))
        stems = [f'RuntimeRoutingZero{slot}Step{i:02}' for i in range(33)]
        name = f'RuntimeRoutingPrecision{slot}Domain'
        source = ''.join(f'import ShielddSecurity.{stem}\n' for stem in stems)
        source += ('set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'
                   f'namespace ShielddSecurity.{name}\n')
        source += 'def tests : List (List Row) := [' + ','.join(s + '.rawRows' for s in stems) + ']\n'
        indices = [precision['onehot_row'], extraction['plan']['constant_link']]
        source += f'def onehotIndices : List Nat := {indices}\n'
        source += 'def onehotRows : List Row := [' + ','.join(_row(raw[i]['a'], raw[i]['b']) for i in indices) + ']\n'
        source += 'def rawRows : List Row := tests.flatten ++ onehotRows\n'
        source += 'def input : Linear := ' + _lc(precision['input']) + '\n'
        for field, label in [('denominator', 'denominator'), ('flag', 'flag'), ('inverse', 'inverse')]:
            source += f'def {label} (index : Nat) : Linear := match index with\n'
            source += ''.join(f'  | {i} => {stem}.{field}\n' for i, stem in enumerate(stems))
            source += '  | _ => []\n'
        source += 'def flags : List Linear := [' + ','.join(stem + '.flag' for stem in stems) + ']\n'
        source += '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem eval_flatten (rho : Nat → F) (lcs : List Linear) :
    eval rho lcs.flatten = RoutingPrecision.sum (lcs.map (eval rho)) := by
  induction lcs with
  | nil => rfl
  | cons head tail ih => simp only [List.flatten_cons,eval_append,List.map_cons,RoutingPrecision.sum,ih]
private theorem tests_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : ∀ index ∈ List.range 33,
    eval rho (denominator index) * eval rho (inverse index) = 1 - eval rho (flag index) ∧
      eval rho (denominator index) * eval rho (flag index) = 0 := by
  intro index member
  have bound := List.mem_range.mp member
  have choices : ''' + ' ∨ '.join(f'index = {i}' for i in range(33)) + ''' := by omega
  rcases choices with ''' + ' | '.join('rfl' for _ in range(33)) + '\n'
        for index, stem in enumerate(stems):
            source += f'''  · have localRows : Satisfies rho {stem}.rawRows := by
      intro row member
      apply satisfied row
      apply List.mem_append_left
      apply List.mem_flatten.mpr
      exact ⟨{stem}.rawRows, {_member(index)}, member⟩
    exact ⟨{stem}.inverse_sound rho one four localRows, {stem}.zero_sound rho one four localRows⟩
'''
        source += '''private theorem denominator_meaning (rho : Nat → F) (one : rho 0 = 1)
    (index : Nat) (member : index ∈ List.range 33) :
    eval rho (denominator index) = eval rho input - (index : F) := by
  have checked : (List.range 33).all (fun index => decide
    (Compiler.canonical Scalar.modulus (denominator index) =
      Compiler.canonical Scalar.modulus (input ++ [(0,-(index : Int))]))) = true := by decide
  have meaning := Compiler.canonical_equal rho _ _
    (of_decide_eq_true (List.all_eq_true.mp checked index member))
  simpa only [eval_append,eval,Int.cast_neg,Int.cast_natCast,one,one_mul,mul_one,add_zero,
    sub_eq_add_neg] using meaning
private theorem onehot_sound (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows) :
    RoutingPrecision.sum ((List.range 33).map (fun index => eval rho (flag index))) = 1 := by
  have localRows : Satisfies rho onehotRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  have normalized := Compiler.unoutline_rows_sound rho 200692 onehotRows localRows (by decide)
  let expected : List Row := [⟨Compiler.subtract flags.flatten [(0,1)],[]⟩]
  have oriented : Satisfies rho expected :=
    RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows 200692 onehotRows)
      expected (by decide) normalized
  have equation := Compiler.checked_assertion_sound rho expected flags.flatten [(0,1)] oriented (by decide)
  have shape : (List.range 33).map flag = flags := by decide
  have mapped := congrArg (fun lcs : List Linear => lcs.map (eval rho)) shape
  have sumShape : (List.range 33).map (fun index => eval rho (flag index)) = flags.map (eval rho) := by
    simpa only [List.map_map,Function.comp_def] using mapped
  rw [sumShape, ← eval_flatten]
  simpa only [eval,Int.cast_one,one_mul,add_zero,one] using equation
theorem domain_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ precision : Nat, precision < 33 ∧ eval rho input = (precision : F) := by
  have equations := tests_sound rho one four satisfied
  apply RoutingPrecision.precision_sound (eval rho input) (fun index => eval rho (flag index))
    (fun index => eval rho (inverse index))
  · intro index member
    rw [← denominator_meaning rho one index member]
    exact (equations index member).1
  · intro index member
    rw [← denominator_meaning rho one index member]
    exact (equations index member).2
  · exact onehot_sound rho one satisfied
theorem flags_sound [DecidableEq F] (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : ∀ index ∈ List.range 33,
    eval rho (flag index) = if eval rho input = (index : F) then 1 else 0 := by
  intro index member
  have equations := tests_sound rho one four satisfied index member
  have meaning := RoutingPrecision.zero_test_sound _ _ _ equations.1 equations.2
  rw [denominator_meaning rho one index member] at meaning
  simpa only [sub_eq_zero] using meaning
'''
        for export in ['domain_sound', 'flags_sound']:
            source += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        result[name] = source + f'end ShielddSecurity.{name}\n'
    assert len(result) == 2
    return result
