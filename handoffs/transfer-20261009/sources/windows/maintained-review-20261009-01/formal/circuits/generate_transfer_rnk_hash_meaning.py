"""Small consumer of retained hash constructors and hash-only sound endpoints.

No permutation graph is rendered here. Typed actual observation/row acceptance
is performed by transfer_rnk_hash.generate_sponge_join(include_selection=False).
The resulting proof derives its row satisfaction from the three constructors.
"""
from .generate_hash_round import _signature_audits


def generate():
    name = 'RuntimeRnkHashMeaningCompletion'
    source = '''import ShielddSecurity.RuntimeRnkHashOnly
import ShielddSecurity.RuntimeRnkHashSequenceCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeRnkHashMeaningCompletion
variable {F : Type} [Field F] [CharP F Scalar.modulus]

theorem hash_rows_complete (base : Nat → F) (linked : base 200692 = base 0) :
    Satisfies (RuntimeRnkHashSequenceCompletion.completed base) RuntimeRnkHashOnly.rawRows := by
  have done := RuntimeRnkHashSequenceCompletion.complete_rows base linked
  intro row member
  simp only [RuntimeRnkHashOnly.rawRows,List.mem_append,List.not_mem_nil,or_false] at member
  rcases member with (first | second) | third
  · have included := List.all_eq_true.mp
      RuntimeTransferRnkHash0OwnedCompletion.sound_coverage_checked row first
    exact done row (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (of_decide_eq_true included)))))
  · have included := List.all_eq_true.mp
      RuntimeTransferRnkHash1OwnedCompletion.sound_coverage_checked row second
    exact done row (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr (of_decide_eq_true included)))))
  · have included := List.all_eq_true.mp
      RuntimeTransferRnkHash2OwnedCompletion.sound_coverage_checked row third
    exact done row (List.mem_append.mpr (Or.inr (of_decide_eq_true included)))

theorem inputs_preserved (base : Nat → F) :
    RuntimeRnkHashOnly.inputs.map (eval (RuntimeRnkHashSequenceCompletion.completed base)) = RuntimeRnkHashOnly.inputs.map (eval base) := by
  have checked : RuntimeRnkHashOnly.inputs.all (fun terms => terms.all
    (fun term => decide (term.1 < 60778 ∨ 61929 < term.1))) = true := by decide
  apply List.map_congr_left
  intro terms member
  apply RuntimeRnkHashSequenceCompletion.eval_preserved
  intro term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked terms member) term present)

theorem actual_rnk_hash (base : Nat → F) (one : base 0 = 1)
    (linked : base 200692 = base 0) :
    eval (RuntimeRnkHashSequenceCompletion.completed base) RuntimeRnkHashOnly.output = Poseidon.hash6
      (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters)
      17 (RuntimeRnkHashOnly.inputs.map (eval base)) := by
  have completedOne : RuntimeRnkHashSequenceCompletion.completed base 0 = 1 :=
    (RuntimeRnkHashSequenceCompletion.preserves base 0 (by omega)).trans one
  have result := RuntimeRnkHashOnly.actual_rnk_hash (RuntimeRnkHashSequenceCompletion.completed base) completedOne (hash_rows_complete base linked)
  rw [inputs_preserved base] at result
  exact result

theorem actual_rnk_commitment (base : Nat → F) (one : base 0 = 1)
    (linked : base 200692 = base 0) :
    eval (RuntimeRnkHashSequenceCompletion.completed base) RuntimeRnkHashOnly.commitment = Poseidon.hash3
      (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation2_0.parameters)
      18 [Poseidon.hash6
        (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters)
        17 (RuntimeRnkHashOnly.inputs.map (eval base))] := by
  have completedOne : RuntimeRnkHashSequenceCompletion.completed base 0 = 1 :=
    (RuntimeRnkHashSequenceCompletion.preserves base 0 (by omega)).trans one
  have result := RuntimeRnkHashOnly.actual_rnk_commitment (RuntimeRnkHashSequenceCompletion.completed base) completedOne (hash_rows_complete base linked)
  rw [actual_rnk_hash base one linked] at result
  exact result
'''
    for export in ('hash_rows_complete','inputs_preserved','actual_rnk_hash','actual_rnk_commitment'):
        source += '#print axioms '+export+'\n'
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
