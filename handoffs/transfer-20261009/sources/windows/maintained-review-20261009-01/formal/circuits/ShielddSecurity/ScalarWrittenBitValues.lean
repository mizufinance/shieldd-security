import ShielddSecurity.Rows

set_option maxHeartbeats 100000

namespace ShielddSecurity.ScalarWrittenBitValues

theorem field_bit_value {F : Type} [Field F] (base : Nat → F)
    (start : Nat) (bits : List Bool) (index : Nat) (bound : index < bits.length) :
    writeBits base start bits (start+index) =
      (if bits[index]?.getD false then (1 : F) else 0) := by
  have lower : start ≤ start+index := by omega
  have upper : start+index < start+bits.length := by omega
  have position : start+index-start = index := by omega
  simp only [writeBits, if_pos (And.intro lower upper), position]

theorem preserved_bit_value {F : Type} [Field F] (base rho : Nat → F)
    (start : Nat) (bits : List Bool)
    (preserved : ∀ column ∈ List.range' start bits.length,
      rho column = writeBits base start bits column)
    (index : Nat) (bound : index < bits.length) :
    rho (start+index) = (if bits[index]?.getD false then (1 : F) else 0) := by
  have member : start+index ∈ List.range' start bits.length := by
    exact List.mem_range'.mpr ⟨index,bound,by simp only [Nat.one_mul]⟩
  exact (preserved _ member).trans (field_bit_value base start bits index bound)

set_option pp.all true in
#check @field_bit_value
#print axioms field_bit_value
set_option pp.all true in
#check @preserved_bit_value
#print axioms preserved_bit_value

end ShielddSecurity.ScalarWrittenBitValues
