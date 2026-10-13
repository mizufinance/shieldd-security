import Mathlib.GroupTheory.Index

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.DoublingKernelBound01

variable {J : Type} [AddCommGroup J]

theorem kernel_composition_bound [Finite J] (left right : J →+ J) :
    Nat.card (left.comp right).ker ≤ Nat.card left.ker * Nat.card right.ker := by
  let projection : (left.comp right).ker →+ left.ker := {
    toFun := fun point => ⟨right point, point.property⟩
    map_zero' := by apply Subtype.ext; exact right.map_zero
    map_add' := by intro x y; apply Subtype.ext; exact right.map_add x y
  }
  let equivalence : projection.ker ≃ right.ker := {
    toFun := fun point => ⟨point.val.val,
      congrArg (fun value : left.ker => (value : J)) point.property⟩
    invFun := fun point => ⟨⟨point.val, by
      change left (right point.val) = 0
      rw [point.property, left.map_zero]⟩, by
        apply Subtype.ext
        exact point.property⟩
    left_inv := by intro point; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro point; apply Subtype.ext; rfl
  }
  have product : Nat.card (left.comp right).ker =
      Nat.card projection.ker * Nat.card projection.range := by
    rw [← AddSubgroup.index_ker projection]
    exact (AddSubgroup.card_mul_index projection.ker).symm
  have rangeBound : Nat.card projection.range ≤ Nat.card left.ker :=
    Nat.card_le_card_of_injective (fun value : projection.range => (value : left.ker))
      Subtype.val_injective
  calc
    Nat.card (left.comp right).ker = Nat.card right.ker * Nat.card projection.range := by
      rw [product, Nat.card_congr equivalence]
    _ ≤ Nat.card right.ker * Nat.card left.ker := Nat.mul_le_mul_left _ rangeBound
    _ = Nat.card left.ker * Nat.card right.ker := Nat.mul_comm _ _

def multiply (n : Nat) : J →+ J := nsmulAddMonoidHom n

theorem multiplication_composition (a b : Nat) :
    (multiply (J := J) a).comp (multiply b) = multiply (a * b) := by
  ext point
  change a • (b • point) = (a * b) • point
  rw [Nat.mul_comm a b, mul_nsmul]

theorem doubling_kernel_step [Finite J] (n : Nat) (twoBound : Nat.card (multiply (J := J) 2).ker ≤ 2) :
    Nat.card (multiply (J := J) (2 * n)).ker ≤ 2 * Nat.card (multiply (J := J) n).ker := by
  have bound := kernel_composition_bound (multiply (J := J) 2) (multiply (J := J) n)
  rw [multiplication_composition] at bound
  exact bound.trans (Nat.mul_le_mul_right _ twoBound)

/-- A symbolic recurrence bounds every repeated doubling kernel. -/
theorem power_two_kernel_bound [Finite J] (k : Nat)
    (twoBound : Nat.card (multiply (J := J) 2).ker ≤ 2) :
    Nat.card (multiply (J := J) (2 ^ k)).ker ≤ 2 ^ k := by
  induction k with
  | zero =>
    have kernelOne : (multiply (J := J) 1).ker = ⊥ := by
      ext point
      simp [multiply]
    simp [kernelOne]
  | succ k previous =>
    have step := doubling_kernel_step (J := J) (2 ^ k) twoBound
    have bound := step.trans (Nat.mul_le_mul_left 2 previous)
    simpa only [Nat.pow_succ, Nat.mul_comm] using bound

theorem kernel_eight_bound [Finite J] (twoBound : Nat.card (multiply (J := J) 2).ker ≤ 2) :
    Nat.card (multiply (J := J) 8).ker ≤ 8 :=
  power_two_kernel_bound 3 twoBound

end ShielddSecurity.DoublingKernelBound01

set_option pp.all true in
#check @ShielddSecurity.DoublingKernelBound01.kernel_composition_bound
#print axioms ShielddSecurity.DoublingKernelBound01.kernel_composition_bound
set_option pp.all true in
#check @ShielddSecurity.DoublingKernelBound01.multiply
#print axioms ShielddSecurity.DoublingKernelBound01.multiply
set_option pp.all true in
#check @ShielddSecurity.DoublingKernelBound01.multiplication_composition
#print axioms ShielddSecurity.DoublingKernelBound01.multiplication_composition
set_option pp.all true in
#check @ShielddSecurity.DoublingKernelBound01.doubling_kernel_step
#print axioms ShielddSecurity.DoublingKernelBound01.doubling_kernel_step
set_option pp.all true in
#check @ShielddSecurity.DoublingKernelBound01.power_two_kernel_bound
#print axioms ShielddSecurity.DoublingKernelBound01.power_two_kernel_bound
set_option pp.all true in
#check @ShielddSecurity.DoublingKernelBound01.kernel_eight_bound
#print axioms ShielddSecurity.DoublingKernelBound01.kernel_eight_bound
