import ShielddSecurity.RuntimeTransferEpk0Canonical
import ShielddSecurity.ScalarEncodedReflection

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEpkCanonicalReflection

/-- Exact source positions in the captured scope-zero canonical word. -/
theorem source_positions : RuntimeTransferEpk0Canonical.bits =
    (List.range 252).map (fun index => [(4931 + index, (1 : Int))]) := by
  decide

/-- Reflect an arbitrary satisfying assignment through its actual Boolean rows.
The scalar is decoded from the assignment rather than supplied as a bit premise. -/
theorem source_bit_value {F : Type} [Field F] [CharP F RuntimeTransferEpk0Canonical.p]
    (rho : Nat → F) (satisfied : Satisfies rho RuntimeTransferEpk0Canonical.originalRows)
    (index : Nat) (bound : index < 252) :
    eval rho [(4931 + index, 1)] =
      (if (encodeBits 252 (binary (RuntimeTransferEpk0Canonical.decodedBits rho)))[index]?.getD false
        then 1 else 0) := by
  have position : RuntimeTransferEpk0Canonical.bits[index]? = some [(4931 + index, 1)] := by
    rw [source_positions]
    simp only [List.getElem?_map, List.getElem?_range bound, Option.map_some]
  have member := List.mem_of_getElem? position
  have unoutlined : Satisfies rho RuntimeTransferEpk0Canonical.rows :=
    Compiler.unoutline_rows_sound rho RuntimeTransferEpk0Canonical.copyColumn
      RuntimeTransferEpk0Canonical.originalRows satisfied RuntimeTransferEpk0Canonical.checked_copy
  have checked : ScalarBits.checkBits RuntimeTransferEpk0Canonical.p
      RuntimeTransferEpk0Canonical.rows RuntimeTransferEpk0Canonical.bits = true :=
    RuntimeTransferEpk0Canonical.checked_bits
  have boolean : Square (eval rho [(4931 + index, 1)]) (eval rho [(4931 + index, 1)]) :=
    Compiler.checked_row_sound rho RuntimeTransferEpk0Canonical.rows
      ⟨[(4931 + index, 1)], [(4931 + index, 1)]⟩ unoutlined
      ((List.all_eq_true.mp checked) _ member)
  have width : RuntimeTransferEpk0Canonical.bits.length = 252 := by
    rw [source_positions]
    simp only [List.length_map, List.length_range]
  exact ScalarEncodedReflection.source_bit_value rho RuntimeTransferEpk0Canonical.bits
    252 index [(4931 + index, 1)] width position boolean

set_option pp.all true in
#check @source_positions
#print axioms source_positions
set_option pp.all true in
#check @source_bit_value
#print axioms source_bit_value

end ShielddSecurity.TransferEpkCanonicalReflection
