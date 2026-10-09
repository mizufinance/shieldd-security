import ShielddSecurity.ShielddHexJsonByteGuards
import ShielddSecurity.ShielddHexStringOperations

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddJsonPlainBorrow

/- Scalar first-special-byte recurrence of serde_json::skip_to_escape_slow.
The optimized word scan must be joined separately using its actual word mask
and first-hit position. This module never assumes a selected scan answer. -/
def firstEscape : List Nat → Nat
  | [] => 0
  | code :: rest => if ShielddHexJsonByteGuards.isEscape code then 0 else 1 + firstEscape rest

theorem first_escape_after_plain (plain suffix : List Nat)
    (neutral : ∀ code ∈ plain, ShielddHexJsonByteGuards.isEscape code = false) :
    firstEscape (plain ++ suffix) = plain.length + firstEscape suffix := by
  induction plain with
  | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons code rest ih =>
    have head := neutral code (List.mem_cons_self)
    have tail : ∀ next ∈ rest, ShielddHexJsonByteGuards.isEscape next = false := by
      intro next member
      exact neutral next (List.mem_cons_of_mem code member)
    simp only [List.cons_append, firstEscape, head, Bool.false_eq_true, if_false,
      List.length_cons, ih tail]
    omega

theorem closing_quote_selected (plain suffix : List Nat)
    (neutral : ∀ code ∈ plain, ShielddHexJsonByteGuards.isEscape code = false) :
    firstEscape (plain ++ 34 :: suffix) = plain.length := by
  rw [first_escape_after_plain plain (34 :: suffix) neutral]
  have quote : ShielddHexJsonByteGuards.isEscape 34 = true := by decide
  simp [firstEscape, quote]

/- Empty-scratch quote branch only. None means the no-escape borrowed branch
is unavailable (escape handler/control/EOF); it does not declare Rust's
general escape-capable JSON parser to reject every non-plain string. -/
def plainBorrow (input : List Nat) (start : Nat) : Option (List Nat × Nat) :=
  let unread := input.drop start
  let count := firstEscape unread
  if (unread.drop count).head? = some 34 then
    some (unread.take count, start + count + 1)
  else none

theorem borrowed_slice_exact (before plain suffix : List Nat)
    (neutral : ∀ code ∈ plain, ShielddHexJsonByteGuards.isEscape code = false) :
    plainBorrow (before ++ (plain ++ 34 :: suffix)) before.length =
      some (plain, before.length + plain.length + 1) := by
  simp [plainBorrow, List.drop_left, closing_quote_selected plain suffix neutral, List.take_left]

theorem hex_literal_borrowed (before suffix : List Nat) (bytes : List GroupByteCodec.Byte) :
    plainBorrow (before ++ (ShielddHexStringOperations.encodedString bytes ++ 34 :: suffix))
      before.length = some (ShielddHexCodec.encode bytes, before.length + 2 * bytes.length + 1) := by
  rw [ShielddHexStringOperations.hex_string_bytes]
  rw [borrowed_slice_exact before _ suffix (ShielddHexJsonByteGuards.encoded_no_escape bytes)]
  rw [ShielddHexCodec.encode_length]

theorem borrowed_cursor_bounds (before plain suffix : List Nat)
    (neutral : ∀ code ∈ plain, ShielddHexJsonByteGuards.isEscape code = false) :
    ∃ content cursor,
      plainBorrow (before ++ (plain ++ 34 :: suffix)) before.length = some (content, cursor) ∧
      content = plain ∧ cursor = before.length + plain.length + 1 ∧
      cursor ≤ (before ++ (plain ++ 34 :: suffix)).length := by
  refine ⟨plain, before.length + plain.length + 1,
    borrowed_slice_exact before plain suffix neutral, rfl, rfl, ?_⟩
  simp only [List.length_append, List.length_cons]
  omega

set_option pp.all true in
#check @first_escape_after_plain
#print axioms first_escape_after_plain
set_option pp.all true in
#check @closing_quote_selected
#print axioms closing_quote_selected
set_option pp.all true in
#check @borrowed_slice_exact
#print axioms borrowed_slice_exact
set_option pp.all true in
#check @hex_literal_borrowed
#print axioms hex_literal_borrowed
set_option pp.all true in
#check @borrowed_cursor_bounds
#print axioms borrowed_cursor_bounds

end ShielddSecurity.ShielddJsonPlainBorrow
