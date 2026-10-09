"""Interpret captured32 prefix sums using the already derived33 selectors."""
from pathlib import Path
from .generate_transfer_routing_zero_rows import _lc


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-row-derivative-v1'
    original = (Path(__file__).resolve().parent/'ShielddSecurity/RoutingPrecision.lean').read_text()
    zero = original[original.index('private theorem sum_map_zero'):original.index('/-- Onehot')]
    single = original[original.index('private theorem sum_indicator'):original.index('/-- A legal native precision')]
    theory = ('import ShielddSecurity.RoutingPrecision\nset_option maxHeartbeats 300000\n'
              'namespace ShielddSecurity.RuntimeRoutingPrefixTheory\n'
              'variable {F : Type} [Field F]\n' + zero + single)
    theory += '''theorem indicator_sum (indices : List Nat) (target : Nat) (unique : indices.Nodup) :
    RoutingPrecision.sum (indices.map (fun index => if index = target then (1 : F) else 0)) =
      if target ∈ indices then 1 else 0 := by
  by_cases present : target ∈ indices
  · rw [if_pos present]
    exact sum_indicator indices target unique present
  · rw [if_neg present]
    apply sum_map_zero
    intro index member
    have different : index ≠ target := by
      intro equal
      exact present (equal ▸ member)
    exact if_neg different
set_option pp.all true in
#check @indicator_sum
#print axioms indicator_sum
end ShielddSecurity.RuntimeRoutingPrefixTheory
'''
    # Reuse the exact existing finite sum recurrences under their qualified name.
    theory = theory.replace('    sum ', '    RoutingPrecision.sum ').replace('= sum ', '= RoutingPrecision.sum ')
    theory = theory.replace('List.map_cons, sum,', 'List.map_cons, RoutingPrecision.sum,')
    result = {'RuntimeRoutingPrefixTheory': theory}
    for slot, plan in enumerate(extraction['plan']['precision']):
        assert len(plan['prefix']) == 32 and len(plan['matches']) == 33
        domain = f'RuntimeRoutingPrecision{slot}Domain'
        name = f'RuntimeRoutingPrecision{slot}Prefix'
        source = (f'import ShielddSecurity.{domain}\n'
                  'import ShielddSecurity.RuntimeRoutingPrefixTheory\n'
                  'set_option maxHeartbeats 1000000\nset_option maxRecDepth 4096\n'
                  f'namespace ShielddSecurity.{name}\n')
        source += 'def prefix (index : Nat) : Linear := match index with\n'
        source += ''.join(f'  | {index} => {_lc(terms)}\n' for index, terms in enumerate(plan['prefix']))
        source += '  | _ => []\n'
        source += '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem eval_flatten (rho : Nat → F) (lcs : List Linear) :
    eval rho lcs.flatten = RoutingPrecision.sum (lcs.map (eval rho)) := by
  induction lcs with
  | nil => rfl
  | cons head tail ih => simp only [List.flatten_cons,eval_append,List.map_cons,RoutingPrecision.sum,ih]
theorem integer_flags (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho D.rawRows) (precision : Nat) (legal : precision < 33)
    (input : eval rho D.input = (precision : F)) : ∀ index ∈ List.range 33,
    eval rho (D.flag index) = if index = precision then 1 else 0 := by
  classical
  intro index member
  have observed := D.flags_sound rho one four satisfied index member
  have capacity : 33 < Scalar.modulus := by decide
  have equalities : (precision : F) = (index : F) ↔ index = precision := by
    constructor
    · intro equality
      exact (bounded_cast_injective (legal.trans capacity) ((List.mem_range.mp member).trans capacity) equality).symm
    · intro equality
      rw [equality]
  simpa only [input,equalities] using observed
theorem prefix_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho D.rawRows) (precision : Nat) (legal : precision < 33)
    (input : eval rho D.input = (precision : F)) (index : Nat) (bound : index < 32) :
    eval rho (prefix index) = if index < precision then 1 else 0 := by
  have checked : (List.range 32).all (fun index => decide
    (((List.range' (index+1) (32-index)).map D.flag).flatten = prefix index)) = true := by decide
  have shape := of_decide_eq_true (List.all_eq_true.mp checked index (List.mem_range.mpr bound))
  rw [← shape,eval_flatten]
  have mapped : ((List.range' (index+1) (32-index)).map D.flag).map (eval rho) =
      (List.range' (index+1) (32-index)).map (fun point => if point = precision then (1 : F) else 0) := by
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro point member
    apply integer_flags rho one four satisfied precision legal input point
    apply List.mem_range.mpr
    have interval := List.mem_range'.mp member
    omega
  rw [mapped,RuntimeRoutingPrefixTheory.indicator_sum _ precision (List.nodup_range')]
  have present : precision ∈ List.range' (index+1) (32-index) ↔ index < precision := by
    simp only [List.mem_range']
    omega
  rw [present]
'''
        source = source.replace('D.', domain+'.')
        for export in ['integer_flags', 'prefix_sound']:
            source += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        result[name] = source + f'end ShielddSecurity.{name}\n'
    assert len(result) == 3
    return result
