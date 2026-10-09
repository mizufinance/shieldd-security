import ShielddSecurity.Compiler

set_option maxHeartbeats 150000
namespace ShielddSecurity.RowOrientationSoundness

/-- Either orientation of a left square polynomial gives the same row truth.
The finite checker must cover every requested source row, including duplicates. -/
theorem checked_rows {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (actual expected : List Row)
    (checked : expected.all (fun row => Compiler.checkRow p actual row ||
      Compiler.checkRow p actual ⟨scaleLinear (-1) row.a,row.b⟩) = true)
    (satisfied : Satisfies rho actual) : Satisfies rho expected := by
  intro row member
  have check := List.all_eq_true.mp checked row member
  simp only [Bool.or_eq_true] at check
  rcases check with direct | reversed
  · exact Compiler.checked_row_sound rho actual row satisfied direct
  · have truth := Compiler.checked_row_sound rho actual
      ⟨scaleLinear (-1) row.a,row.b⟩ satisfied reversed
    simpa only [eval_scale,Int.cast_neg,Int.cast_one,neg_one_mul,Square,neg_mul_neg] using truth

set_option pp.all true in
#check @checked_rows
#print axioms checked_rows
end ShielddSecurity.RowOrientationSoundness
