import ShielddSecurity.ScalarBits

set_option maxHeartbeats 150000

namespace ShielddSecurity.ScalarBooleanReflection

/-- Symbolic word meaning from direct Boolean row consequences. Concrete
callers can use row membership rather than repeat a quadratic row search. -/
theorem word_value {F : Type} [Field F] (rho : Nat → F) (bits : List Linear)
    (booleans : ∀ bit ∈ bits, Square (eval rho bit) (eval rho bit)) :
    eval rho (ScalarBits.bitLinear bits) =
      (binary (ScalarBits.decodeBits rho bits) : F) := by
  classical
  have mapValue : bits.map (eval rho) =
      (ScalarBits.decodeBits rho bits).map (fun bit => if bit then (1 : F) else 0) := by
    simp only [ScalarBits.decodeBits, List.map_map]
    apply List.map_congr_left
    intro bit member
    exact ScalarBits.decoded_bit_value rho bit (booleans bit member)
  rw [ScalarBits.eval_bitLinear, mapValue, binary_cast]

private theorem weighted_value {F : Type} [Field F] (rho : Nat → F)
    (columns : List Nat) (weight : Int) :
    eval rho (weighted columns weight) =
      (weight : F) * fieldBinary (columns.map rho) := by
  induction columns generalizing weight with
  | nil => simp [weighted, eval, fieldBinary]
  | cons column columns ih =>
      simp only [weighted, eval, List.map_cons, fieldBinary, ih, Int.cast_mul,
        Int.cast_ofNat]
      ring

/-- The integer is decoded from arbitrary satisfying physical bit rows.
The reconstruction equation is also a row consequence. -/
theorem columns_value {F : Type} [Field F] (rho : Nat → F)
    (columns : List Nat) (value : Nat)
    (booleans : Satisfies rho (columns.map booleanRow))
    (reconstruction : Square (eval rho (reconstructionRow value columns).a)
      (eval rho (reconstructionRow value columns).b)) :
    ∃ n : Nat, n < 2 ^ columns.length ∧ (n : F) = rho value := by
  have bits : ∀ x ∈ columns.map rho, Square x x := by
    intro x member
    obtain ⟨column, present, rfl⟩ := List.mem_map.mp member
    have truth := booleans (booleanRow column) (List.mem_map.mpr ⟨column, present, rfl⟩)
    simpa only [booleanRow, eval, Int.cast_one, one_mul, mul_zero, add_zero] using truth
  have equation : fieldBinary (columns.map rho) = rho value := by
    have zero := square_zero _ reconstruction
    simp only [reconstructionRow, eval, Int.cast_neg, Int.cast_one, neg_one_mul,
      weighted_value, one_mul] at zero
    calc
      fieldBinary (columns.map rho) =
        rho value + (-rho value + fieldBinary (columns.map rho)) := by ring
      _ = rho value := by rw [zero, add_zero]
  obtain ⟨n, bound, meaning⟩ := range_sound (columns.map rho) (rho value) bits equation
  exact ⟨n, by simpa only [List.length_map] using bound, meaning⟩

set_option pp.all true in
#check @word_value
#print axioms word_value
set_option pp.all true in
#check @columns_value
#print axioms columns_value

end ShielddSecurity.ScalarBooleanReflection
