import ShielddSecurity.ReceiverLifecycleWordShape

set_option maxHeartbeats 200000

namespace ShielddSecurity.ReceiverLifecycleFieldStatus

variable {F : Type} [Field F]

theorem boolean_injective (a b : Bool)
    (same : (if a then (1 : F) else 0) = (if b then 1 else 0)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Project the same reconstructed Boolean word onto any physical column. -/
theorem mapped_value (rho : Nat → F) (columns : List Nat) (bits : List Bool)
    (width : columns.length = bits.length)
    (values : columns.map rho = bits.map (fun bit => if bit then (1 : F) else 0))
    (i : Nat) (inside : i < columns.length) :
    rho columns[i] = if bits[i]'(by omega) then 1 else 0 := by
  have leftBound : i < (columns.map rho).length := by simpa using inside
  have rightBound : i < (bits.map (fun bit => if bit then (1 : F) else 0)).length := by
    simpa only [List.length_map,← width] using inside
  have projected := congrArg (fun word : List F => word[i]?.getD 0) values
  dsimp only at projected
  rw [List.getElem?_eq_getElem leftBound,List.getElem?_eq_getElem rightBound] at projected
  simpa only [Option.getD_some,List.getElem_map] using projected

/-- The physical zero product with enabled multiplier one forces the bit;
the bit value comes from the proved word, rather than a constructed assignment. -/
theorem enabled_product (flag value : F) (bit expected : Bool)
    (enabled : flag = 1)
    (meaning : value = if bit then 1 else 0)
    (product : flag * (value - (if expected then 1 else 0)) = 0) : bit = expected := by
  rw [enabled,one_mul] at product
  apply boolean_injective (F := F) bit expected
  exact meaning.symm.trans (sub_eq_zero.mp product)

/-- Only three status bits and a symbolic high suffix are needed for Active. -/
theorem status_active (bits : List Bool) (width : bits.length = 131)
    (low0 : bits[0]'(by omega) = true)
    (low1 : bits[1]'(by omega) = false)
    (low2 : bits[2]'(by omega) = false)
    (high : ∀ i,67 ≤ i → (inside : i < bits.length) → bits[i] = false) :
    ReceiverLifecycle.LegalActive (binary bits) := by
  apply ReceiverLifecycleWordShape.active bits width
  · apply List.ext_getElem
    · simp [width]
    · intro i leftBound rightBound
      have small : i < 3 := by simpa [width] using leftBound
      have casesIndex : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases casesIndex with rfl | rfl | rfl <;> simp_all
  · intro bit member
    obtain ⟨i,inside,same⟩ := List.mem_iff_getElem.mp member
    have bound : i + 67 < bits.length := by
      have remaining := inside
      simp only [List.length_drop] at remaining
      omega
    have zero := high (i + 67) (by omega) bound
    have dropZero : (bits.drop 67)[i] = false := by
      simpa only [List.getElem_drop,Nat.add_comm] using zero
    exact same.symm.trans dropZero

set_option pp.all true in
#check @boolean_injective
#print axioms boolean_injective
set_option pp.all true in
#check @mapped_value
#print axioms mapped_value
set_option pp.all true in
#check @enabled_product
#print axioms enabled_product
set_option pp.all true in
#check @status_active
#print axioms status_active

end ShielddSecurity.ReceiverLifecycleFieldStatus
