import ShielddSecurity.RuntimeTransferSignedBalanceSoundness
import ShielddSecurity.ScalarWordColumn

set_option maxHeartbeats 200000
namespace ShielddSecurity.RuntimeTransferSignedBalanceWordSoundness

theorem canonical_word {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho RuntimeTransferSignedBalanceCompletion.rawRows) :
    ∃ n : Nat, n < 2^129 ∧ (n : F) = rho 21712 ∧
      (List.range' 21713 129).map rho = (encodeBits 129 n).map (fun bit => if bit then (1 : F) else 0) := by
  have booleans : Satisfies rho (RuntimeTransferSignedBalanceCompletion.bitColumns.map booleanRow) := by
    rw [← RuntimeTransferSignedBalanceCompletion.boolean_identity]
    intro row member
    exact satisfied row (by
      simp only [RuntimeTransferSignedBalanceCompletion.rawRows,RuntimeTransferSignedBalanceCompletion.rawRangeRows,
        List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl member)))
  have expected := RuntimeTransferSignedBalanceSoundness.expected_from_actual rho satisfied
  have reconstructed := expected (reconstructionRow 21712 RuntimeTransferSignedBalanceCompletion.bitColumns)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
  have result := ScalarBooleanCanonical.columns_word rho RuntimeTransferSignedBalanceCompletion.bitColumns
    21712 booleans reconstructed
  simpa only [RuntimeTransferSignedBalanceCompletion.bitColumns,List.length_range'] using result

theorem bit_value {F : Type} [Field F] (rho : Nat → F) (n index : Nat) (bound : index < 129)
    (word : (List.range' 21713 129).map rho = (encodeBits 129 n).map (fun bit => if bit then (1 : F) else 0)) :
    rho (21713 + index) = (if (encodeBits 129 n)[index]?.getD false then 1 else 0) :=
  ScalarWordColumn.consecutive rho 21713 129 (encodeBits 129 n) (encodeBits_length 129 n) word index bound

set_option pp.all true in
#check @canonical_word
#print axioms canonical_word
set_option pp.all true in
#check @bit_value
#print axioms bit_value
end ShielddSecurity.RuntimeTransferSignedBalanceWordSoundness
