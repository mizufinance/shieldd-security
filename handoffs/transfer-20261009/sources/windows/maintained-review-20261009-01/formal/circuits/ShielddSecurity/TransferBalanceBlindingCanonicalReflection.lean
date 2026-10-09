import ShielddSecurity.RuntimeBalanceBlindingCanonical
import ShielddSecurity.ScalarEncodedReflection

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceBlindingCanonicalReflection

/-- Exact source positions in the captured balance blinding canonical word. -/
theorem source_positions : RuntimeBalanceBlindingCanonical.bits =
    (List.range 252).map (fun index => [(22232 + index, (1 : Int))]) := by
  decide

/-- Reflect an arbitrary satisfying assignment through its actual Boolean rows.
The scalar is decoded from the assignment rather than supplied as a bit premise. -/
theorem source_bit_value {F : Type} [Field F] [CharP F RuntimeBalanceBlindingCanonical.p]
    (rho : Nat → F) (satisfied : Satisfies rho RuntimeBalanceBlindingCanonical.originalRows)
    (index : Nat) (bound : index < 252) :
    eval rho [(22232 + index, 1)] =
      (if (encodeBits 252 (binary (RuntimeBalanceBlindingCanonical.decodedBits rho)))[index]?.getD false
        then 1 else 0) := by
  have position : RuntimeBalanceBlindingCanonical.bits[index]? = some [(22232 + index, 1)] := by
    rw [source_positions]
    simp only [List.getElem?_map, List.getElem?_range bound, Option.map_some]
  have member := List.mem_of_getElem? position
  have unoutlined : Satisfies rho RuntimeBalanceBlindingCanonical.rows :=
    Compiler.unoutline_rows_sound rho RuntimeBalanceBlindingCanonical.copyColumn
      RuntimeBalanceBlindingCanonical.originalRows satisfied RuntimeBalanceBlindingCanonical.checked_copy
  have checked : ScalarBits.checkBits RuntimeBalanceBlindingCanonical.p
      RuntimeBalanceBlindingCanonical.rows RuntimeBalanceBlindingCanonical.bits = true :=
    RuntimeBalanceBlindingCanonical.checked_bits
  have boolean : Square (eval rho [(22232 + index, 1)]) (eval rho [(22232 + index, 1)]) :=
    Compiler.checked_row_sound rho RuntimeBalanceBlindingCanonical.rows
      ⟨[(22232 + index, 1)], [(22232 + index, 1)]⟩ unoutlined
      ((List.all_eq_true.mp checked) _ member)
  have width : RuntimeBalanceBlindingCanonical.bits.length = 252 := by
    rw [source_positions]
    simp only [List.length_map, List.length_range]
  exact ScalarEncodedReflection.source_bit_value rho RuntimeBalanceBlindingCanonical.bits
    252 index [(22232 + index, 1)] width position boolean

set_option pp.all true in
#check @source_positions
#print axioms source_positions
set_option pp.all true in
#check @source_bit_value
#print axioms source_bit_value

end ShielddSecurity.TransferBalanceBlindingCanonicalReflection
