import ShielddSecurity.RowRenaming
import ShielddSecurity.ScalarBits

set_option maxHeartbeats 150000

namespace ShielddSecurity.EncryptionDhScalar

/-- Transport a bit reader under the actual EPK column map. -/
theorem decode_bit {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Nat) (bit : Linear) :
    ScalarBits.decodeBit (fun column => rho (columns column)) bit =
      ScalarBits.decodeBit rho (RowRenaming.linear columns bit) := by
  classical
  simp only [ScalarBits.decodeBit, RowRenaming.eval_linear]

theorem decode_bits {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Nat) (bits : List Linear) :
    ScalarBits.decodeBits (fun column => rho (columns column)) bits =
      ScalarBits.decodeBits rho (bits.map (RowRenaming.linear columns)) := by
  simp only [ScalarBits.decodeBits, List.map_map]
  apply List.map_congr_left
  intro bit member
  exact decode_bit rho columns bit

/-- This identifies integer readers only. The EPK's actual comparison,
reconstruction and nonidentity rows must separately derive its scalar bounds. -/
theorem scalar_agrees {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Nat) (source actual : List Linear)
    (checked : source.map (RowRenaming.linear columns) = actual) :
    binary (ScalarBits.decodeBits (fun column => rho (columns column)) source) =
      binary (ScalarBits.decodeBits rho actual) := by
  rw [decode_bits, checked]

set_option pp.all true in
#check @decode_bit
#print axioms decode_bit
set_option pp.all true in
#check @decode_bits
#print axioms decode_bits
set_option pp.all true in
#check @scalar_agrees
#print axioms scalar_agrees

end ShielddSecurity.EncryptionDhScalar
