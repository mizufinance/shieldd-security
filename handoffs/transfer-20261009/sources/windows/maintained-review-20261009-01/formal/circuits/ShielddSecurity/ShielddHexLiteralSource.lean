import ShielddSecurity.ShielddHexChunkSource
import ShielddSecurity.ShielddJsonPlainBorrow

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddHexLiteralSource

open ShielddHexJsonWordDetector ShielddHexChunkSource

theorem chunk_count (count : Nat) (bytes : List Nat) :
    (chunkViews count bytes).length = count := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih => simp only [chunkViews, List.length_cons, ih]

theorem chunk_flatten (count : Nat) (bytes : List Nat) :
    (chunkViews count bytes).flatten = bytes.take (8 * count) := by
  induction count generalizing bytes with
  | zero => simp only [chunkViews, List.flatten_nil, Nat.mul_zero, List.take_zero]
  | succ count ih =>
    simp only [chunkViews, List.flatten_cons, ih]
    rw [Nat.mul_succ, Nat.add_comm (8 * count) 8, List.take_add]

theorem chunk_members (count : Nat) (bytes : List Nat) (word : List Nat)
    (member : word ∈ chunkViews count bytes) (byte : Nat) (inWord : byte ∈ word) :
    byte ∈ bytes := by
  induction count generalizing bytes with
  | zero => simp only [chunkViews, List.not_mem_nil] at member
  | succ count ih =>
    simp only [chunkViews, List.mem_cons] at member
    rcases member with same | tail
    · subst word
      exact List.mem_of_mem_take inWord
    · exact List.mem_of_mem_drop (ih (bytes.drop 8) tail)

theorem chunk_widths (count : Nat) (bytes : List Nat)
    (enough : 8 * count ≤ bytes.length) :
    ∀ word ∈ chunkViews count bytes, word.length = 8 := by
  induction count generalizing bytes with
  | zero => intro word member; simp only [chunkViews, List.not_mem_nil] at member
  | succ count ih =>
    have head : 8 ≤ bytes.length := by omega
    have tail : 8 * count ≤ (bytes.drop 8).length := by
      simp only [List.length_drop]
      omega
    intro word member
    simp only [chunkViews, List.mem_cons] at member
    rcases member with same | member
    · subst word
      exact List.length_take_of_le head
    · exact ih (bytes.drop 8) tail word member

/- Derive every word view and complete-chunk count from the raw64-byte body.
No chosen seven-word projection, word mask, or cursor answer is a premise.
The suffix may contain arbitrary subsequent JSON; the first quote exits
before any suffix word is examined. -/
theorem raw_quote_from_bytes (plain suffix : List Nat) (contentStart : Nat)
    (length : plain.length = 64) (safe : ∀ byte ∈ plain, SafeByte byte) :
    rawWordLoop (contentStart + 1)
      ((plain.drop 1 ++ 34 :: suffix).length / 8)
      (plain.drop 1 ++ 34 :: suffix) = some (contentStart + 64) := by
  let unread := plain.drop 1
  let words := chunkViews 7 unread
  let leading := unread.drop 56
  have unreadLength : unread.length = 63 := by simp [unread, length]
  have count : words.length = 7 := chunk_count 7 unread
  have widths : ∀ word ∈ words, word.length = 8 :=
    chunk_widths 7 unread (by omega)
  have wordSafe : ∀ word ∈ words, ∀ byte ∈ word, SafeByte byte := by
    intro word member byte inWord
    exact safe byte (List.mem_of_mem_drop (chunk_members 7 unread word member byte inWord))
  have leadingLength : leading.length = 7 := by simp [leading, unreadLength]
  have leadingSafe : ∀ byte ∈ leading, SafeByte byte := by
    intro byte member
    exact safe byte (List.mem_of_mem_drop (List.mem_of_mem_drop member))
  have split : words.flatten ++ leading = unread := by
    rw [chunk_flatten 7 unread]
    exact List.take_append_drop 56 unread
  have input : unread ++ 34 :: suffix =
      words.flatten ++ ((leading ++ [34]) ++ suffix) := by
    rw [← split]
    simp only [List.append_assoc, List.singleton_append]
  have fuel : (unread ++ 34 :: suffix).length / 8 =
      words.length + (suffix.length / 8 + 1) := by
    simp only [List.length_append, List.length_cons, unreadLength, count]
    omega
  change rawWordLoop (contentStart + 1)
    ((unread ++ 34 :: suffix).length / 8) (unread ++ 34 :: suffix) = _
  rw [fuel, input]
  exact raw_coefficient_quote_cursor contentStart words leading suffix
    (suffix.length / 8) count widths wordSafe leadingLength leadingSafe

/- The actual source codec renderer supplies its bytes constructively.
Native String/array/slice primitive bindings remain explicit; no raw JSON
decoder-success or per-table coefficient result is assumed here. -/
theorem encoded_source_borrow (before suffix : List Nat) (bytes : GroupByteCodec.Bytes) :
    let content := ShielddHexStringOperations.encodedString (List.ofFn bytes)
    rawWordLoop (before.length + 1)
      ((content.drop 1 ++ 34 :: suffix).length / 8)
      (content.drop 1 ++ 34 :: suffix) = some (before.length + 64) ∧
    ShielddJsonPlainBorrow.plainBorrow (before ++ (content ++ 34 :: suffix))
      before.length = some (ShielddHexCodec.encode (List.ofFn bytes), before.length + 65) := by
  let content := ShielddHexStringOperations.encodedString (List.ofFn bytes)
  have length : content.length = 64 := by
    simp only [content, ShielddHexStringOperations.hex_string_length, List.length_ofFn]
  have safe : ∀ byte ∈ content, SafeByte byte := by
    dsimp only [content]
    rw [ShielddHexStringOperations.hex_string_bytes]
    exact encoded_conditions (List.ofFn bytes)
  refine ⟨raw_quote_from_bytes content suffix before.length length safe, ?_⟩
  simpa only [List.length_ofFn] using
    ShielddJsonPlainBorrow.hex_literal_borrowed before suffix (List.ofFn bytes)

set_option pp.all true in
#check @chunk_count
#print axioms chunk_count
set_option pp.all true in
#check @chunk_flatten
#print axioms chunk_flatten
set_option pp.all true in
#check @chunk_members
#print axioms chunk_members
set_option pp.all true in
#check @chunk_widths
#print axioms chunk_widths
set_option pp.all true in
#check @raw_quote_from_bytes
#print axioms raw_quote_from_bytes
set_option pp.all true in
#check @encoded_source_borrow
#print axioms encoded_source_borrow

end ShielddSecurity.ShielddHexLiteralSource
