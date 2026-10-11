import ShielddSecurity.TransferSourceOrderedDriver01
import Init.Data.Nat.Compare
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarReversedByteOrder01
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferCanonicalWordEquality01 (CanonicalScalar)
/-! Symbolic high-byte-first lexicographic UInt8 comparison of reversed
exact source bytes. Equal-width lists derive mathematical comparison with
no caller ordering assumption. Canonical internal domain also aligns compare
Eq with raw words. Rust iterator cmp/u8 primitives, Scalar invariant and Ord
trait/collection bindings remain explicit; no native/certification credit. -/

def compareHighFirst : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: rest, right :: tail =>
    match compare left.toNat right.toNat with
    | .eq => compareHighFirst rest tail
    | ordering => ordering

theorem bounded_low_byte_comparison_is_dominated_by_upper_value
    (left right upperLeft upperRight : Nat) (leftBound : left < 256) (rightBound : right < 256) :
    compare (left + 256 * upperLeft) (right + 256 * upperRight) =
      match compare upperLeft upperRight with
      | .eq => compare left right
      | ordering => ordering := by
  cases upper : compare upperLeft upperRight with
  | lt =>
    have less := Nat.compare_eq_lt.mp upper
    exact Nat.compare_eq_lt.mpr (by omega)
  | gt =>
    have less := Nat.compare_eq_gt.mp upper
    exact Nat.compare_eq_gt.mpr (by omega)
  | eq =>
    have same := Nat.compare_eq_eq.mp upper
    subst upperRight
    simp only [Nat.compare_eq_ite_lt, Nat.add_lt_add_iff_right]

theorem equal_width_lexical_append_compares_suffix_only_after_equal_prefix
    (left right : List UInt8) (width : left.length = right.length) (lastLeft lastRight : UInt8) :
    compareHighFirst (left ++ [lastLeft]) (right ++ [lastRight]) =
      match compareHighFirst left right with
      | .eq => compare lastLeft.toNat lastRight.toNat
      | ordering => ordering := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail => simp only [List.length_nil, List.length_cons] at width; omega
  | cons head rest ih =>
    cases right with
    | nil => simp only [List.length_nil, List.length_cons] at width; omega
    | cons other tail =>
      have tails : rest.length = tail.length := Nat.succ.inj width
      simp only [List.cons_append, compareHighFirst]
      rw [ih tail tails]
      cases compare head.toNat other.toNat <;> rfl

theorem reversed_typed_byte_lexical_comparison_is_exact_numeric_comparison
    (left right : List UInt8) (width : left.length = right.length) :
    compareHighFirst left.reverse right.reverse = compare (decodeLE left) (decodeLE right) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail => simp only [List.length_nil, List.length_cons] at width; omega
  | cons head rest ih =>
    cases right with
    | nil => simp only [List.length_nil, List.length_cons] at width; omega
    | cons other tail =>
      have tails : rest.length = tail.length := Nat.succ.inj width
      rw [List.reverse_cons, List.reverse_cons,
        equal_width_lexical_append_compares_suffix_only_after_equal_prefix _ _ (by simp only [List.length_reverse]; exact tails),
        ih tail tails]
      exact (bounded_low_byte_comparison_is_dominated_by_upper_value head.toNat other.toNat
        (decodeLE rest) (decodeLE tail) head.toNat_lt other.toNat_lt).symm

theorem source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order
    (left right : Vector UInt64 4) :
    compareHighFirst (serializerBytes left.toList).reverse (serializerBytes right.toList).reverse =
      compare (montgomeryValue left) (montgomeryValue right) := by
  rw [reversed_typed_byte_lexical_comparison_is_exact_numeric_comparison _ _ (by
    rw [TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList,
      TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList])]
  change compare (scalarKey left) (scalarKey right) = compare (montgomeryValue left) (montgomeryValue right)
  rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]

theorem canonical_source_reversed_byte_compare_eq_iff_raw_words_equal (left right : CanonicalScalar) :
    compareHighFirst (serializerBytes left.words.toList).reverse (serializerBytes right.words.toList).reverse = .eq ↔
      left.words = right.words := by
  rw [source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order, Nat.compare_eq_eq]
  exact TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal left right

theorem source_reversed_byte_compare_lt_iff_mathematical_value_lt (left right : Vector UInt64 4) :
    compareHighFirst (serializerBytes left.toList).reverse (serializerBytes right.toList).reverse = .lt ↔
      montgomeryValue left < montgomeryValue right := by
  rw [source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order, Nat.compare_eq_lt]

theorem source_reversed_byte_compare_gt_iff_mathematical_value_gt (left right : Vector UInt64 4) :
    compareHighFirst (serializerBytes left.toList).reverse (serializerBytes right.toList).reverse = .gt ↔
      montgomeryValue right < montgomeryValue left := by
  rw [source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order, Nat.compare_eq_gt]

set_option pp.all true in
#check @compareHighFirst
#print axioms compareHighFirst
set_option pp.all true in
#check @bounded_low_byte_comparison_is_dominated_by_upper_value
#print axioms bounded_low_byte_comparison_is_dominated_by_upper_value
set_option pp.all true in
#check @equal_width_lexical_append_compares_suffix_only_after_equal_prefix
#print axioms equal_width_lexical_append_compares_suffix_only_after_equal_prefix
set_option pp.all true in
#check @reversed_typed_byte_lexical_comparison_is_exact_numeric_comparison
#print axioms reversed_typed_byte_lexical_comparison_is_exact_numeric_comparison
set_option pp.all true in
#check @source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order
#print axioms source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order
set_option pp.all true in
#check @canonical_source_reversed_byte_compare_eq_iff_raw_words_equal
#print axioms canonical_source_reversed_byte_compare_eq_iff_raw_words_equal
set_option pp.all true in
#check @source_reversed_byte_compare_lt_iff_mathematical_value_lt
#print axioms source_reversed_byte_compare_lt_iff_mathematical_value_lt
set_option pp.all true in
#check @source_reversed_byte_compare_gt_iff_mathematical_value_gt
#print axioms source_reversed_byte_compare_gt_iff_mathematical_value_gt
end ShielddSecurity.TransferScalarReversedByteOrder01
