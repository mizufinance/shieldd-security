"""Symbolic reversed-byte lexical order equals actual serializer mathematical order."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
source='''import ShielddSecurity.TransferSourceOrderedDriver01
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
    | nil => simp only [List.nil_append, compareHighFirst]; cases compare lastLeft.toNat lastRight.toNat <;> rfl
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

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarReversedByteOrder01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarReversedByteOrder01.lean').write_text(source)
s=(DIAG/'transfer-source-ordered-driver-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-source-ordered-finalizer-20261011-03'", "UPSTREAM = DIAG / 'transfer-source-ordered-driver-20261011-01'")
replace("POOL = DIAG / 'transfer-source-ordered-driver-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-reversed-byte-order-owned-floor-20261011-03'")
replace("MODULE = 'TransferSourceOrderedDriver01'", "MODULE = 'TransferScalarReversedByteOrder01'")
replace("stdout = UPSTREAM / 'runs/01-TransferSourceOrderedFinalizer01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferSourceOrderedDriver01/stdout.txt'")
replace('assert len(current) == 7','assert len(current) == 4')
replace("records.append(('TransferSourceOrderedFinalizer01'", "records.append(('TransferSourceOrderedDriver01'")
replace("    'handwritten/TransferSourceOrderedFinalizer01.lean', 'project/ShielddSecurity/TransferSourceOrderedFinalizer01.lean']]", "    'handwritten/TransferSourceOrderedDriver01.lean', 'project/ShielddSecurity/TransferSourceOrderedDriver01.lean']]")
replace('assert len(records) == 103 and len(audits) == 924','assert len(records) == 104 and len(audits) == 928')
replace("'objects': 103", "'objects': 104")
s=s.replace('one-hundred-three-module','one-hundred-four-module').replace('924 inherited','928 inherited')
replace("'imports': ['ShielddSecurity.TransferSourceOrderedFinalizer01']", "'imports': ['ShielddSecurity.TransferSourceOrderedDriver01','Init.Data.Nat.Compare']")
replace('assert len(names) == 4','assert len(names) == 8');replace("'fresh_audits': 4", "'fresh_audits': 8")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Symbolic reversed high-byte-first lexical UInt8 comparison derives exact decoded integer comparison for arbitrary equal-width byte lists and all fixed source32byte serializer vectors. Canonical internal domain additionally makes compare Eq iff raw words equal; Lt/Gt iff mathematical value strict order. Eight complete reports one definition/seven theorems, symbolic recurrences no wide walk. Rust iterator cmp/u8 primitive/Scalar invariant/Ord trait/collection/compiler/cache/full trace binding remains explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SOURCE_ORDERED_DRIVER_COMPLETE_ONE_HUNDRED_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','REVERSED_BYTE_ORDER_COMPLETE_ONE_HUNDRED_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 924", "'inherited_audits': 928")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':928,'owned_modules':104,'native_order_binding_open':True})
