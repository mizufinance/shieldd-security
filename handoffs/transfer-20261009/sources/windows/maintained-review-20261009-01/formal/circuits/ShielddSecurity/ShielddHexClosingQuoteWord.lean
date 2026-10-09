import ShielddSecurity.ShielddHexWordBoundary
import ShielddSecurity.ShielddHexJsonWordDetector

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddHexClosingQuoteWord

open ShielddHexJsonByteGuards ShielddHexJsonWordOperations
open ShielddHexJsonWordDetector ShielddHexWordBoundary

/- The literal 64-bit native detector, with all three wrapping subtractions.
Exact seven-leading-byte + quote source shape is derived from the64-character
coefficient, the initial skip increment and eight-byte chunk iteration;
these operational/source associations are kept separately from this algebra. -/
def wordMask (bytes : List Nat) : Nat :=
  let chars := packed bytes
  let quote := chars ^^^ (34 * oneBytes 8)
  let slash := chars ^^^ (92 * oneBytes 8)
  (((wrappedSub (2 ^ 64) chars (32 * oneBytes 8)) &&& complement 8 chars) |||
    ((wrappedSub (2 ^ 64) quote (oneBytes 8)) &&& complement 8 quote) |||
    ((wrappedSub (2 ^ 64) slash (oneBytes 8)) &&& complement 8 slash)) &&& highMask 8

theorem closing_word_mask (leading : List Nat) (length : leading.length = 7)
    (safe : ∀ byte ∈ leading, SafeByte byte) : wordMask (leading ++ [34]) = 2 ^ 63 := by
  let bytes := leading ++ [34]
  have count : bytes.length = 8 := by simp [bytes, length]
  have controlSafe : ∀ byte ∈ bytes, 32 ≤ byte ∧ byte < 128 := by
    intro byte member
    simp only [bytes, List.mem_append, List.mem_singleton] at member
    rcases member with member | same
    · exact (safe byte member).1
    · subst byte; decide
  have bounds : ∀ byte ∈ bytes, byte < 256 := by
    intro byte member; have := (controlSafe byte member).2; omega
  have packedBound : packed bytes < 2 ^ 64 := by
    have derived := packed_bound bytes bounds
    simpa only [count] using derived
  have controlEnough : 32 * oneBytes 8 ≤ packed bytes := by
    simpa only [count] using packed_enough bytes 32 (fun byte member => (controlSafe byte member).1)
  have control : ((wrappedSub (2 ^ 64) (packed bytes) (32 * oneBytes 8)) &&&
      complement 8 (packed bytes)) &&& highMask 8 = 0 := by
    rw [wrapped_no_borrow _ _ _ controlEnough packedBound]
    simpa only [count] using masked_subtraction_zero bytes 32 (complement 8 (packed bytes))
      (fun byte member => (controlSafe byte member).1)
      (fun byte member => by have := (controlSafe byte member).2; omega)
  have slashSafe : ∀ byte ∈ bytes, 1 ≤ byte ^^^ 92 ∧ byte ^^^ 92 < 128 := by
    intro byte member
    simp only [bytes, List.mem_append, List.mem_singleton] at member
    rcases member with member | same
    · exact (safe byte member).2.2
    · subst byte; decide
  let slashBytes := bytes.map (fun byte => byte ^^^ 92)
  have slashCount : slashBytes.length = 8 := by simp [slashBytes, count]
  have slashEnough : ∀ value ∈ slashBytes, 1 ≤ value := by
    intro value member
    obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
    exact (slashSafe byte inBytes).1
  have slashBounds : ∀ value ∈ slashBytes, value < 256 := by
    intro value member
    obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
    have := (slashSafe byte inBytes).2; omega
  have slashPackedBound : packed slashBytes < 2 ^ 64 := by
    have derived := packed_bound slashBytes slashBounds
    simpa only [slashCount] using derived
  have slashPackedEnough : oneBytes 8 ≤ packed slashBytes := by
    simpa only [slashCount, Nat.one_mul] using packed_enough slashBytes 1 slashEnough
  have slashEq : packed bytes ^^^ (92 * oneBytes 8) = packed slashBytes := by
    simpa only [count] using packed_xor_constant bytes 92 (by decide) bounds
  have slash : ((wrappedSub (2 ^ 64) (packed bytes ^^^ (92 * oneBytes 8)) (oneBytes 8)) &&&
      complement 8 (packed bytes ^^^ (92 * oneBytes 8))) &&& highMask 8 = 0 := by
    rw [slashEq, wrapped_no_borrow _ _ _ slashPackedEnough slashPackedBound]
    simpa only [slashCount, Nat.one_mul] using masked_subtraction_zero slashBytes 1
      (complement 8 (packed slashBytes)) slashEnough (fun value member => by
        obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
        have := (slashSafe byte inBytes).2; omega)
  let quoteBytes := leading.map (fun byte => byte ^^^ 34)
  have quoteCount : quoteBytes.length = 7 := by simp [quoteBytes, length]
  have quoteEnough : ∀ value ∈ quoteBytes, 1 ≤ value := by
    intro value member
    obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
    exact (safe byte inBytes).2.1.1
  have quoteBounds : ∀ value ∈ quoteBytes, value < 256 := by
    intro value member
    obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
    have := (safe byte inBytes).2.1.2; omega
  have quotePackedBound : packed quoteBytes < 2 ^ 56 := by
    have derived := packed_bound quoteBytes quoteBounds
    simpa only [quoteCount] using derived
  have quotePackedEnough : oneBytes 7 ≤ packed quoteBytes := by
    simpa only [quoteCount, Nat.one_mul] using packed_enough quoteBytes 1 quoteEnough
  have quoteEq : packed bytes ^^^ (34 * oneBytes 8) = packed quoteBytes := by
    rw [← count, packed_xor_constant bytes 34 (by decide) bounds]
    simp [bytes, quoteBytes, packed_append, packed]
  let lowComplement := (2 ^ 56 - 1) ^^^ packed quoteBytes
  have lowComplementBound : lowComplement < 2 ^ 56 :=
    Nat.xor_lt_two_pow (by decide) quotePackedBound
  have quoteComplement : complement 8 (packed quoteBytes) = lowComplement + 2 ^ 56 * 255 := by
    change ((2 ^ 56 - 1) + 2 ^ 56 * 255) ^^^ (packed quoteBytes + 2 ^ 56 * 0) = _
    rw [block_join_xor 56 _ _ 255 0 (by decide) quotePackedBound]
    simp only [Nat.xor_zero, lowComplement]
  have deltaBound : packed quoteBytes - oneBytes 7 < 2 ^ 56 := by omega
  have lowMaskZero : (((packed quoteBytes - oneBytes 7) &&& lowComplement) &&& highMask 7) = 0 := by
    simpa only [quoteCount, Nat.one_mul] using masked_subtraction_zero quoteBytes 1 lowComplement
      quoteEnough (fun value member => by
        obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
        have := (safe byte inBytes).2.1.2; omega)
  have highSplit : highMask 8 = highMask 7 + 2 ^ 56 * 128 := by decide
  have highBound : highMask 7 < 2 ^ 56 := by decide
  have lowAndBound : (packed quoteBytes - oneBytes 7) &&& lowComplement < 2 ^ 56 :=
    lt_of_le_of_lt Nat.and_le_left deltaBound
  have quote : ((wrappedSub (2 ^ 64) (packed bytes ^^^ (34 * oneBytes 8)) (oneBytes 8)) &&&
      complement 8 (packed bytes ^^^ (34 * oneBytes 8))) &&& highMask 8 = 2 ^ 63 := by
    rw [quoteEq, wrapped_closing_quote _ quotePackedEnough quotePackedBound, quoteComplement, highSplit]
    rw [block_join_and 56 _ _ 255 255 deltaBound lowComplementBound]
    rw [block_join_and 56 _ _ (255 &&& 255) 128 lowAndBound highBound, lowMaskZero]
    decide
  change wordMask bytes = _
  unfold wordMask
  rw [Nat.and_or_distrib_right, Nat.and_or_distrib_right, control, quote, slash]
  simp only [Nat.zero_or, Nat.or_zero]

theorem closing_word_position (leading : List Nat) (length : leading.length = 7)
    (safe : ∀ byte ∈ leading, SafeByte byte) :
    trailingBits 64 (wordMask (leading ++ [34])) / 8 = 7 := by
  rw [closing_word_mask leading length safe]
  exact closing_mask_position

set_option pp.all true in
#check @closing_word_mask
#print axioms closing_word_mask
set_option pp.all true in
#check @closing_word_position
#print axioms closing_word_position

end ShielddSecurity.ShielddHexClosingQuoteWord
