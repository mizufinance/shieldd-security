import ShielddSecurity.ShielddHexScannerSequence

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddHexChunkSource

open ShielddHexJsonWordOperations ShielddHexWordBoundary
open ShielddHexJsonWordDetector ShielddHexClosingQuoteWord ShielddHexScannerSequence

/- Ordered take/drop views of Rust's chunks_exact(8). The fuel is the number
of complete chunks selected from the unread slice. A short suffix is retained
for the separate scalar fallback; none below means only that the word loop
did not select an escape. Memory/pointer/compiler primitive correspondence
is an explicit source boundary, not a whole scanner-return premise. -/
def chunkViews : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | count + 1, bytes => bytes.take 8 :: chunkViews count (bytes.drop 8)

def wordLoop : Nat → List (List Nat) → Option Nat
  | _, [] => none
  | cursor, word :: remaining =>
      if wordMask word = 0 then wordLoop (cursor + 8) remaining
      else some (cursor + trailingBits 64 (wordMask word) / 8)

def rawWordLoop (cursor completeChunks : Nat) (unread : List Nat) : Option Nat :=
  wordLoop cursor (chunkViews completeChunks unread)

theorem take_eight_word (word suffix : List Nat) (length : word.length = 8) :
    (word ++ suffix).take 8 = word := by
  rw [← length]
  exact List.take_left

theorem drop_eight_word (word suffix : List Nat) (length : word.length = 8) :
    (word ++ suffix).drop 8 = suffix := by
  rw [← length]
  exact List.drop_left

theorem chunk_views_exact (words : List (List Nat)) (suffix : List Nat)
    (remaining : Nat) (lengths : ∀ word ∈ words, word.length = 8) :
    chunkViews (words.length + remaining) (words.flatten ++ suffix) =
      words ++ chunkViews remaining suffix := by
  induction words with
  | nil => simp only [List.length_nil, Nat.zero_add, List.flatten_nil,
      List.nil_append]
  | cons word rest ih =>
    have head := lengths word List.mem_cons_self
    have tail : ∀ next ∈ rest, next.length = 8 := by
      intro next member
      exact lengths next (List.mem_cons_of_mem word member)
    rw [List.flatten_cons, List.append_assoc]
    simp only [List.length_cons, Nat.add_right_comm rest.length 1 remaining,
      chunkViews, take_eight_word word _ head, drop_eight_word word _ head,
      ih tail, List.cons_append]

/- The source body carries an absolute pointer-derived cursor. The older
scanner recurrence carries a relative offset. This unbounded induction joins
them without assuming either loop's result. -/
theorem word_loop_offsets (words : List (List Nat)) (cursor : Nat) :
    wordLoop cursor words = (scanWords words).map (fun offset => cursor + offset) := by
  induction words generalizing cursor with
  | nil => rfl
  | cons word rest ih =>
    by_cases zero : wordMask word = 0
    · simp only [wordLoop, scanWords, if_pos zero, ih, Option.map_map]
      congr 1
      funext offset
      exact Nat.add_assoc cursor 8 offset
    · simp only [wordLoop, scanWords, if_neg zero, Option.map_some]

theorem raw_word_stage (words : List (List Nat)) (suffix : List Nat)
    (remaining cursor : Nat) (lengths : ∀ word ∈ words, word.length = 8) :
    rawWordLoop cursor (words.length + remaining) (words.flatten ++ suffix) =
      (scanWords (words ++ chunkViews remaining suffix)).map
        (fun offset => cursor + offset) := by
  unfold rawWordLoop
  rw [chunk_views_exact words suffix remaining lengths]
  exact word_loop_offsets _ cursor

theorem raw_coefficient_quote_cursor (contentStart : Nat) (words : List (List Nat))
    (leading suffix : List Nat) (remaining : Nat)
    (count : words.length = 7)
    (lengths : ∀ word ∈ words, word.length = 8)
    (safe : ∀ word ∈ words, ∀ byte ∈ word, SafeByte byte)
    (leadingLength : leading.length = 7)
    (leadingSafe : ∀ byte ∈ leading, SafeByte byte) :
    rawWordLoop (contentStart + 1) (words.length + (remaining + 1))
      (words.flatten ++ ((leading ++ [34]) ++ suffix)) = some (contentStart + 64) := by
  rw [raw_word_stage words _ (remaining + 1) (contentStart + 1) lengths]
  have quoteLength : (leading ++ [34]).length = 8 := by simp [leadingLength]
  simp only [chunkViews, take_eight_word _ _ quoteLength,
    drop_eight_word _ _ quoteLength]
  rw [safe_words_then_quote words leading _ lengths safe leadingLength leadingSafe,
    count]
  simp [Nat.add_assoc]

set_option pp.all true in
#check @take_eight_word
#print axioms take_eight_word
set_option pp.all true in
#check @drop_eight_word
#print axioms drop_eight_word
set_option pp.all true in
#check @chunk_views_exact
#print axioms chunk_views_exact
set_option pp.all true in
#check @word_loop_offsets
#print axioms word_loop_offsets
set_option pp.all true in
#check @raw_word_stage
#print axioms raw_word_stage
set_option pp.all true in
#check @raw_coefficient_quote_cursor
#print axioms raw_coefficient_quote_cursor

end ShielddSecurity.ShielddHexChunkSource
