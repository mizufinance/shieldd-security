import ShielddSecurity.ShielddHexClosingQuoteWord

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddHexScannerSequence

open ShielddHexJsonByteGuards ShielddHexJsonWordOperations
open ShielddHexJsonWordDetector ShielddHexWordBoundary ShielddHexClosingQuoteWord

/- Independent native word-loop recurrence. Word lists are real successive
eight-byte views; their slice/chunks_exact/pointer construction is an explicit
source obligation. Neither word-mask answers nor chosen cursor results are
assumptions of the consequence proofs below. -/
theorem safe_word_zero (bytes : List Nat) (length : bytes.length = 8)
    (safe : ∀ byte ∈ bytes, SafeByte byte) : wordMask bytes = 0 := by
  have bounds : ∀ byte ∈ bytes, byte < 256 := by
    intro byte member; have := (safe byte member).1.2; omega
  have packedBound : packed bytes < 2 ^ 64 := by
    have derived := packed_bound bytes bounds
    simpa only [length] using derived
  have controlEnough : 32 * oneBytes 8 ≤ packed bytes := by
    simpa only [length] using packed_enough bytes 32 (fun byte member => (safe byte member).1.1)
  have transformed (constant : Nat) (constantBound : constant < 256)
      (enough : ∀ byte ∈ bytes, 1 ≤ byte ^^^ constant)
      (small : ∀ byte ∈ bytes, byte ^^^ constant < 128) :
      wrappedSub (2 ^ 64) (packed bytes ^^^ (constant * oneBytes 8)) (oneBytes 8) =
        (packed bytes ^^^ (constant * oneBytes 8)) - oneBytes 8 := by
    let changed := bytes.map (fun byte => byte ^^^ constant)
    have changedLength : changed.length = 8 := by simp [changed, length]
    have changedEnough : ∀ value ∈ changed, 1 ≤ value := by
      intro value member
      obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
      exact enough byte inBytes
    have changedBounds : ∀ value ∈ changed, value < 256 := by
      intro value member
      obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
      have := small byte inBytes; omega
    have totalEnough : oneBytes 8 ≤ packed changed := by
      simpa only [changedLength, Nat.one_mul] using packed_enough changed 1 changedEnough
    have totalBound : packed changed < 2 ^ 64 := by
      have derived := packed_bound changed changedBounds
      simpa only [changedLength] using derived
    have same : packed bytes ^^^ (constant * oneBytes 8) = packed changed := by
      simpa only [length] using packed_xor_constant bytes constant constantBound bounds
    rw [same]
    exact wrapped_no_borrow _ _ _ totalEnough totalBound
  have quote := transformed 34 (by decide)
    (fun byte member => (safe byte member).2.1.1)
    (fun byte member => (safe byte member).2.1.2)
  have slash := transformed 92 (by decide)
    (fun byte member => (safe byte member).2.2.1)
    (fun byte member => (safe byte member).2.2.2)
  have ordinary : wordMask bytes = detector bytes := by
    unfold wordMask detector
    dsimp only
    rw [length, wrapped_no_borrow _ _ _ controlEnough packedBound, quote, slash]
  exact ordinary.trans (detector_zero bytes safe)

def scanWords : List (List Nat) → Option Nat
  | [] => none
  | word :: rest =>
      if wordMask word = 0 then (scanWords rest).map (fun offset => 8 + offset)
      else some (trailingBits 64 (wordMask word) / 8)

theorem first_quote_word (leading : List Nat) (rest : List (List Nat))
    (length : leading.length = 7) (safe : ∀ byte ∈ leading, SafeByte byte) :
    scanWords ((leading ++ [34]) :: rest) = some 7 := by
  have nonzero : (2 : Nat) ^ 63 ≠ 0 := by decide
  simp only [scanWords, closing_word_mask leading length safe, if_neg nonzero, closing_mask_position]

theorem safe_words_then_quote (words : List (List Nat)) (leading : List Nat)
    (rest : List (List Nat))
    (wordLength : ∀ word ∈ words, word.length = 8)
    (wordSafe : ∀ word ∈ words, ∀ byte ∈ word, SafeByte byte)
    (prefixLength : leading.length = 7)
    (prefixSafe : ∀ byte ∈ leading, SafeByte byte) :
    scanWords (words ++ (leading ++ [34]) :: rest) = some (8 * words.length + 7) := by
  induction words with
  | nil => exact first_quote_word leading rest prefixLength prefixSafe
  | cons word remaining ih =>
    have headLength := wordLength word (List.mem_cons_self)
    have headSafe := wordSafe word (List.mem_cons_self)
    have tailLength : ∀ next ∈ remaining, next.length = 8 := by
      intro next member; exact wordLength next (List.mem_cons_of_mem word member)
    have tailSafe : ∀ next ∈ remaining, ∀ byte ∈ next, SafeByte byte := by
      intro next member; exact wordSafe next (List.mem_cons_of_mem word member)
    have zero := safe_word_zero word headLength headSafe
    have tail := ih tailLength tailSafe
    simp [List.cons_append, scanWords, zero, tail, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/- skip_to_escape already consumed one plain byte before its word loop.
Seven full safe words followed by the quote word therefore return exactly
contentStart+64; parse_str_bytes consumes that quote once to get +65. -/
def sourceCursor (contentStart : Nat) (words : List (List Nat)) : Option Nat :=
  (scanWords words).map (fun offset => contentStart + 1 + offset)

theorem coefficient_quote_cursor (contentStart : Nat) (words : List (List Nat))
    (leading : List Nat) (rest : List (List Nat))
    (wordCount : words.length = 7)
    (wordLength : ∀ word ∈ words, word.length = 8)
    (wordSafe : ∀ word ∈ words, ∀ byte ∈ word, SafeByte byte)
    (prefixLength : leading.length = 7) (prefixSafe : ∀ byte ∈ leading, SafeByte byte) :
    sourceCursor contentStart (words ++ (leading ++ [34]) :: rest) = some (contentStart + 64) := by
  unfold sourceCursor
  rw [safe_words_then_quote words leading rest wordLength wordSafe prefixLength prefixSafe, wordCount]
  simp [Nat.add_assoc]

set_option pp.all true in
#check @safe_word_zero
#print axioms safe_word_zero
set_option pp.all true in
#check @first_quote_word
#print axioms first_quote_word
set_option pp.all true in
#check @safe_words_then_quote
#print axioms safe_words_then_quote
set_option pp.all true in
#check @coefficient_quote_cursor
#print axioms coefficient_quote_cursor

end ShielddSecurity.ShielddHexScannerSequence
