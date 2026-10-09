import ShielddSecurity.RowLinearSubstitution
import ShielddSecurity.RowOrientationSoundness
import ShielddSecurity.ScalarBits

set_option maxHeartbeats 200000

namespace ShielddSecurity.RowLinearSubstitutionSoundness

/-- Transport complete source rows under one assignment, allowing the two
orientations of the actual squared input polynomial. -/
theorem checked_rows {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (columns : Nat → Linear) (source actual : List Row)
    (checked : (source.map (RowLinearSubstitution.row columns)).all (fun item =>
      Compiler.checkRow p actual item ||
      Compiler.checkRow p actual ⟨scaleLinear (-1) item.a, item.b⟩) = true)
    (satisfied : Satisfies rho actual) :
    Satisfies (fun column => eval rho (columns column)) source := by
  have mapped := RowOrientationSoundness.checked_rows rho actual
    (source.map (RowLinearSubstitution.row columns)) checked satisfied
  intro item member
  exact RowLinearSubstitution.satisfied_row rho columns item
    (mapped _ (List.mem_map.mpr ⟨item, member, rfl⟩))

/-- This is an equality of readers under the induced assignment. Boolean row
truth and scalar reconstruction remain separate obligations. -/
theorem decode_bit {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Linear) (bit : Linear) :
    ScalarBits.decodeBit (fun column => eval rho (columns column)) bit =
      ScalarBits.decodeBit rho (RowLinearSubstitution.linear columns bit) := by
  classical
  simp only [ScalarBits.decodeBit, RowLinearSubstitution.eval_linear]

theorem decode_bits {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Linear) (bits : List Linear) :
    ScalarBits.decodeBits (fun column => eval rho (columns column)) bits =
      ScalarBits.decodeBits rho (bits.map (RowLinearSubstitution.linear columns)) := by
  simp only [ScalarBits.decodeBits, List.map_map]
  apply List.map_congr_left
  intro bit member
  exact decode_bit rho columns bit

set_option pp.all true in
#check @checked_rows
#print axioms checked_rows
set_option pp.all true in
#check @decode_bit
#print axioms decode_bit
set_option pp.all true in
#check @decode_bits
#print axioms decode_bits

end ShielddSecurity.RowLinearSubstitutionSoundness
