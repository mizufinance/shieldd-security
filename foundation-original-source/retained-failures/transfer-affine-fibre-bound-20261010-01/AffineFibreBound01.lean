import ShielddSecurity.WeierstrassTwoTorsionAlgebra01
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.AffineFibreBound01

variable {F : Type} [Field F]

theorem square_fibre_bound [Fintype F] (right : F) :
    Nat.card {value : F // value * value = right} ≤ 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let roots := Finset.univ.filter (fun value : F => value * value = right)
  change roots.card ≤ 2
  by_cases empty : roots = ∅
  · simp [empty]
  · obtain ⟨root, member⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have rootSquare : root * root = right := (Finset.mem_filter.mp member).2
    have subset : roots ⊆ {root, -root} := by
      intro value present
      have valueSquare : value * value = right := (Finset.mem_filter.mp present).2
      rcases WeierstrassTwoTorsionAlgebra01.equal_square_cases value root
        (valueSquare.trans rootSquare.symm) with same | negative
      · simp [same]
      · simp [negative]
    calc
      roots.card ≤ ({root, -root} : Finset F).card := Finset.card_le_card subset
      _ ≤ 2 := by simpa using Finset.card_insert_le root ({-root} : Finset F)

def solutions_equiv (right : F → F) :
    {xy : F × F // xy.2 * xy.2 = right xy.1} ≃
      (Σ x : F, {y : F // y * y = right x}) where
  toFun point := ⟨point.val.1, ⟨point.val.2, point.property⟩⟩
  invFun point := ⟨(point.1, point.2.val), point.2.property⟩
  left_inv point := by rcases point with ⟨⟨x, y⟩, proof⟩; rfl
  right_inv point := by rcases point with ⟨x, ⟨y, proof⟩⟩; rfl

/-- Symbolic fibre counting, with no enumeration of the huge prime field. -/
theorem affine_solution_bound [Fintype F] (right : F → F) :
    Nat.card {xy : F × F // xy.2 * xy.2 = right xy.1} ≤ 2 * Nat.card F := by
  classical
  rw [Nat.card_congr (solutions_equiv right), Nat.card_eq_fintype_card, Fintype.card_sigma]
  calc
    (∑ x : F, Fintype.card {y : F // y * y = right x}) ≤ ∑ _x : F, 2 := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [Nat.card_eq_fintype_card] using square_fibre_bound (right x)
    _ = 2 * Nat.card F := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

theorem projective_solution_bound [Fintype F] (right : F → F) :
    Nat.card (Option {xy : F × F // xy.2 * xy.2 = right xy.1}) ≤
      2 * Nat.card F + 1 := by
  classical
  have bound := affine_solution_bound right
  rw [Nat.card_eq_fintype_card, Fintype.card_option]
  simpa only [Nat.card_eq_fintype_card] using Nat.add_le_add_right bound 1

end ShielddSecurity.AffineFibreBound01

set_option pp.all true in
#check @ShielddSecurity.AffineFibreBound01.square_fibre_bound
#print axioms ShielddSecurity.AffineFibreBound01.square_fibre_bound
set_option pp.all true in
#check @ShielddSecurity.AffineFibreBound01.solutions_equiv
#print axioms ShielddSecurity.AffineFibreBound01.solutions_equiv
set_option pp.all true in
#check @ShielddSecurity.AffineFibreBound01.affine_solution_bound
#print axioms ShielddSecurity.AffineFibreBound01.affine_solution_bound
set_option pp.all true in
#check @ShielddSecurity.AffineFibreBound01.projective_solution_bound
#print axioms ShielddSecurity.AffineFibreBound01.projective_solution_bound
