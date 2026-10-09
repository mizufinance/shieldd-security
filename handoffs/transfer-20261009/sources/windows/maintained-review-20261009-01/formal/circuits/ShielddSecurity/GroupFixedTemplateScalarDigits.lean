import ShielddSecurity.GroupFixedTemplateTrace

set_option maxHeartbeats 100000

namespace ShielddSecurity.GroupFixedTemplateScalarDigits

theorem digits_word {F : Type} [Field F]
    (windows : List (GroupFixedWindows.FixedWindowWitness F)) (width n : Nat)
    (word : GroupFixedChunks.windowBits windows = encodeBits width n)
    (bound : n < 2 ^ width) :
    TransferWindows.digitsValue (windows.map GroupFixedWindows.fixedDigit) = n := by
  rw [← GroupFixedChunks.window_bits_digits,TransferWindows.pair_digits_value,word]
  exact encodeBits_value width n bound

/-- The first folded digit uses G; the ordinary tail starts with 4G. The bit
word must be certified from the actual window fields at the source boundary. -/
theorem folded_tail_value {F : Type} [Field F] {J : Type} [AddCommGroup J]
    (firstWindow : GroupFixedWindows.FixedWindowWitness F)
    (ordinary : List (GroupFixedWindows.FixedWindowWitness F)) (generator : J)
    (width n : Nat)
    (word : GroupFixedChunks.windowBits (firstWindow :: ordinary) = encodeBits width n)
    (bound : n < 2 ^ width) :
    GroupFixedWindows.fixedDigit firstWindow • generator +
      TransferWindows.digitsValue (ordinary.map GroupFixedWindows.fixedDigit) • (4 • generator) =
      n • generator := by
  have total : GroupFixedWindows.fixedDigit firstWindow +
      4 * TransferWindows.digitsValue (ordinary.map GroupFixedWindows.fixedDigit) = n := by
    simpa only [List.map_cons,TransferWindows.digitsValue] using
      digits_word (firstWindow :: ordinary) width n word bound
  rw [← mul_nsmul,← add_nsmul]
  rw [total]

set_option pp.all true in
#check @digits_word
#print axioms digits_word
set_option pp.all true in
#check @folded_tail_value
#print axioms folded_tail_value

end ShielddSecurity.GroupFixedTemplateScalarDigits
