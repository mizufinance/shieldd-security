import ShielddSecurity.ScalarChunkComposition

set_option maxHeartbeats 200000

namespace ShielddSecurity.ScalarConstructedBits

theorem decoded_singletons {F : Type} [Field F] (rho : Nat → F)
    (columns : List Nat) (bits : List Bool)
    (values : columns.map rho = bits.map (fun bit => if bit then (1 : F) else 0)) :
    ScalarBits.decodeBits rho (columns.map (fun column => [(column,1)])) = bits := by
  classical
  have decoder : (fun bit : Bool => decide ((if bit then (1 : F) else 0) = 1)) = id := by
    funext bit
    cases bit <;> simp
  have decoded := congrArg (List.map (fun value : F => decide (value = 1))) values
  simpa only [ScalarBits.decodeBits,ScalarBits.decodeBit,List.map_map,Function.comp_def,eval,
    Int.cast_one,one_mul,add_zero,decoder,List.map_id] using decoded

/-- Direct bit meanings use the actual write operation, with no integer
uniqueness inference from a modular reconstruction row. -/
theorem decoded_writeBits {F : Type} [Field F] (base : Nat → F)
    (start : Nat) (bits : List Bool) :
    ScalarBits.decodeBits (writeBits base start bits)
      ((List.range' start bits.length).map (fun column => [(column,1)])) = bits :=
  decoded_singletons _ _ bits (writeBits_map base start bits)

/-- Valid at255 bits as well as smaller widths. The final assignment must
preserve each written Boolean column; no field-capacity premise is needed. -/
theorem comparison_from_written_bits {F : Type} [Field F] {p : Nat} [CharP F p]
    (base rho : Nat → F) (start : Nat) (bits : List Bool)
    (rows : List Row) (steps : List ScalarRows.StepData)
    (satisfied : Satisfies rho rows) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (bitOrder : steps.map ScalarRows.StepData.left =
      (List.range' start bits.length).map (fun column => [(column,1)]))
    (preserved : ∀ column ∈ List.range' start bits.length,
      rho column = writeBits base start bits column)
    (booleans : ScalarBits.checkBits p rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain p rows [(0,1)] steps = true) :
    ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left) = bits ∧
      eval rho (ScalarComparisonBounds.endpoint [(0,1)] steps) =
        (if binary bits ≤ binary (steps.map ScalarRows.StepData.right) then 1 else 0) := by
  have mapped : (List.range' start bits.length).map rho =
      (List.range' start bits.length).map (writeBits base start bits) :=
    List.map_congr_left preserved
  have decoded : ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left) = bits := by
    rw [bitOrder]
    exact decoded_singletons rho _ bits (mapped.trans (writeBits_map base start bits))
  have recurrence := ScalarRows.checked_chain_sound rho one four rows satisfied [(0,1)] steps chain
  rw [ScalarComparisonBounds.endpoint_value] at recurrence
  have initial : eval rho [(0,1)] = 1 := by simp [eval,one]
  rw [initial] at recurrence
  have ordered := ScalarBits.polynomial_chain_order rho rows satisfied steps booleans
  have orderDecoded : binary (steps.map (fun step => ScalarBits.decodeBit rho step.left)) = binary bits := by
    simpa only [ScalarBits.decodeBits,List.map_map] using congrArg binary decoded
  rw [orderDecoded] at ordered
  exact ⟨decoded,recurrence.trans ordered⟩

set_option pp.all true in
#check @decoded_singletons
#print axioms decoded_singletons
set_option pp.all true in
#check @decoded_writeBits
#print axioms decoded_writeBits
set_option pp.all true in
#check @comparison_from_written_bits
#print axioms comparison_from_written_bits

end ShielddSecurity.ScalarConstructedBits
