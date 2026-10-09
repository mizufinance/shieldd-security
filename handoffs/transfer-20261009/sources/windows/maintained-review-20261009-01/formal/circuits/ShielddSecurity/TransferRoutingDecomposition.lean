import ShielddSecurity.TransferRoutingBranchCompletion

set_option maxHeartbeats 200000

/-! Reverse routing coverage derives the unique bounded integer tags from their
independent digit equations. The argument recurses on an arbitrary width rather
than unrolling 32 constraints. Full circuit assignment and Rust refinement are
separate obligations. -/
namespace ShielddSecurity.TransferRoutingDecomposition

open TransferCore TransferSem TransferRoutingBranchCompletion

theorem bounded_digits_unique (width a b : Nat)
    (aBound : a < 2 ^ width) (bBound : b < 2 ^ width)
    (digits : ∀ i : Fin width, a / 2 ^ i.val % 2 = b / 2 ^ i.val % 2) : a = b := by
  induction width generalizing a b with
  | zero =>
      simp only [Nat.pow_zero] at aBound bBound
      omega
  | succ width ih =>
      have low := digits ⟨0, Nat.zero_lt_succ width⟩
      simp only [Nat.pow_zero, Nat.div_one] at low
      have aDivision := Nat.mod_add_div a 2
      have bDivision := Nat.mod_add_div b 2
      have aUpper : a < 2 * 2 ^ width := by
        simpa only [Nat.pow_succ'] using aBound
      have bUpper : b < 2 * 2 ^ width := by
        simpa only [Nat.pow_succ'] using bBound
      have aHalf : a / 2 < 2 ^ width := by omega
      have bHalf : b / 2 < 2 ^ width := by omega
      have halves : a / 2 = b / 2 := ih (a / 2) (b / 2) aHalf bHalf (by
        intro i
        have next := digits ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        simpa only [Nat.pow_succ', ← Nat.div_div_eq_div_mul] using next)
      omega

def recoverInputs (c : Crypto) (w : TransferSem.Witness) (legal : RoutingSem c w) :
    LegalRoutingInputs where
  regulatedPrecision := w.routing.regulatedPrecision
  unregulatedPrecision := w.routing.unregulatedPrecision
  height := w.routing.height
  ordered := legal.1
  bounded := legal.2.1

theorem recovered_raw_inputs (c : Crypto) (w : TransferSem.Witness) (legal : RoutingSem c w) :
    (recoverInputs c w legal).regulatedPrecision = w.routing.regulatedPrecision ∧
      (recoverInputs c w legal).unregulatedPrecision = w.routing.unregulatedPrecision ∧
      (recoverInputs c w legal).height = w.routing.height :=
  ⟨rfl, rfl, rfl⟩

theorem tag_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : RoutingSem c w) (slot : Fin 2) :
    (construct c w (recoverInputs c w legal)).tags slot = w.routing.tags slot := by
  have old := legal.2.2.2 slot
  apply bounded_digits_unique 32 _ _ (constructed_tag_bound c w (recoverInputs c w legal) slot) old.1
  intro i
  have oldDigit := old.2 i
  change w.routing.tags slot / 2 ^ i.val % 2 =
    selectedWord c w (recoverInputs c w legal) slot i.val / 2 ^ i.val % 2 at oldDigit
  exact (constructed_tag_bits c w (recoverInputs c w legal) slot i).trans oldDigit.symm

theorem routing_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : RoutingSem c w) : construct c w (recoverInputs c w legal) = w.routing := by
  have parameter := legal.2.2.1
  have tags : (fun slot => binary (bits c w (recoverInputs c w legal) slot)) = w.routing.tags := by
    funext slot
    exact tag_reconstructed c w legal slot
  unfold construct
  rw [tags]
  simp only [recoverInputs]
  rw [← parameter]

theorem full_record_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : RoutingSem c w) : {w with routing := construct c w (recoverInputs c w legal)} = w := by
  rw [routing_reconstructed c w legal]

set_option pp.all true in
#check @bounded_digits_unique
#print axioms bounded_digits_unique
set_option pp.all true in
#check @recovered_raw_inputs
#print axioms recovered_raw_inputs
set_option pp.all true in
#check @tag_reconstructed
#print axioms tag_reconstructed
set_option pp.all true in
#check @routing_reconstructed
#print axioms routing_reconstructed
set_option pp.all true in
#check @full_record_reconstructed
#print axioms full_record_reconstructed

end ShielddSecurity.TransferRoutingDecomposition
