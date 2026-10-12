import ShielddSecurity.TransferCheckedWordPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPendingSaturatingCapacity01
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! The source pending-vector gate uses usize::saturating_add before the
consensus capacity comparison. This finite-width arithmetic model derives
exact unbounded-natural addition acceptance whenever the capacity lies below
the saturation ceiling. Both 32- and 64-bit targets have certified headroom.
Native usize ABI/operator and imbl/vector length correspondence are explicit;
no native, runtime control or certification credit follows from this model. -/

def sourceSaturatingLengthAdd (bits previous additional : Nat) : Nat :=
  min (previous + additional) (2 ^ bits - 1)

theorem finite_width_saturating_gate_iff_exact_natural_sum_bound
    (bits capacity previous additional : Nat) (headroom : capacity < 2 ^ bits - 1) :
    sourceSaturatingLengthAdd bits previous additional ≤ capacity ↔ previous + additional ≤ capacity := by
  constructor
  · intro accepted
    by_cases bounded : previous + additional ≤ 2 ^ bits - 1
    · simpa only [sourceSaturatingLengthAdd, Nat.min_eq_left bounded] using accepted
    · have lower : 2 ^ bits - 1 ≤ previous + additional := Nat.le_of_lt (Nat.lt_of_not_ge bounded)
      have ceiling : 2 ^ bits - 1 ≤ capacity := by
        simpa only [sourceSaturatingLengthAdd, Nat.min_eq_right lower] using accepted
      exact False.elim ((Nat.not_le_of_gt headroom) ceiling)
  · intro accepted
    exact Nat.le_trans (Nat.min_le_left _ _) accepted

theorem consensus_capacity_has_strict_32_and_64_bit_saturation_headroom :
    blockCapacity < 2 ^ 32 - 1 ∧ blockCapacity < 2 ^ 64 - 1 := by
  decide

theorem source_32_and_64_bit_pending_gates_accept_exactly_the_consensus_sum_bound
    (previous additional : Nat) :
    (sourceSaturatingLengthAdd 32 previous additional ≤ blockCapacity ↔ previous + additional ≤ blockCapacity) ∧
      (sourceSaturatingLengthAdd 64 previous additional ≤ blockCapacity ↔ previous + additional ≤ blockCapacity) := by
  exact ⟨finite_width_saturating_gate_iff_exact_natural_sum_bound 32 blockCapacity previous additional
      consensus_capacity_has_strict_32_and_64_bit_saturation_headroom.1,
    finite_width_saturating_gate_iff_exact_natural_sum_bound 64 blockCapacity previous additional
      consensus_capacity_has_strict_32_and_64_bit_saturation_headroom.2⟩

theorem accepted_finite_width_pending_gate_derives_each_length_bound
    (bits capacity previous additional : Nat) (headroom : capacity < 2 ^ bits - 1)
    (accepted : sourceSaturatingLengthAdd bits previous additional ≤ capacity) :
    previous + additional ≤ capacity ∧ previous ≤ capacity ∧ additional ≤ capacity := by
  have exactSum := (finite_width_saturating_gate_iff_exact_natural_sum_bound bits capacity previous additional headroom).mp accepted
  exact ⟨exactSum, Nat.le_trans (Nat.le_add_right previous additional) exactSum,
    Nat.le_trans (Nat.le_add_left additional previous) exactSum⟩

set_option pp.all true in
#check @sourceSaturatingLengthAdd
#print axioms sourceSaturatingLengthAdd
set_option pp.all true in
#check @finite_width_saturating_gate_iff_exact_natural_sum_bound
#print axioms finite_width_saturating_gate_iff_exact_natural_sum_bound
set_option pp.all true in
#check @consensus_capacity_has_strict_32_and_64_bit_saturation_headroom
#print axioms consensus_capacity_has_strict_32_and_64_bit_saturation_headroom
set_option pp.all true in
#check @source_32_and_64_bit_pending_gates_accept_exactly_the_consensus_sum_bound
#print axioms source_32_and_64_bit_pending_gates_accept_exactly_the_consensus_sum_bound
set_option pp.all true in
#check @accepted_finite_width_pending_gate_derives_each_length_bound
#print axioms accepted_finite_width_pending_gate_derives_each_length_bound
end ShielddSecurity.TransferPendingSaturatingCapacity01
