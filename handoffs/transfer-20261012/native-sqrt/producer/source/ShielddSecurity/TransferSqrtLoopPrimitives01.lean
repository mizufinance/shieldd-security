import ShielddSecurity.TransferScalarPredicates01
import ShielddSecurity.TransferScalarChoiceMasks01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferSqrtLoopPrimitives01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarChoiceMasks01 (SourceChoiceByte valid_source_choice_byte_is_exactly_zero_or_one)
open TransferScalarConstantEquality01 (sourceScalarWordsCtEqByte sourceNotChoiceByte)
/-! Exact subtle2.6.1 integer and Choice operations used by the ff0.13.0
Tonelli-Shanks loop. These are source-value mathematics; volatile barrier,
compiler, memory/caller-origin and execution correspondence remain separate. -/

theorem source_u32_high_bit_detects_nonzero (word : UInt32) :
    ((word ||| (-word)) >>> 31) = if word = 0 then 0 else 1 := by
  by_cases zero : word = 0
  · rw [zero] <;> rfl
  · have bounded : word.toNat < 4294967296 := word.toNat_lt
    have positive : 0 < word.toNat := by
      have nonzero : word.toNat ≠ 0 := by
        intro impossible
        exact zero (UInt32.toNat_inj.mp impossible)
      omega
    have negated : (-word).toNat = 4294967296 - word.toNat := by
      rw [UInt32.toNat_neg]
      change (4294967296 - word.toNat) % 4294967296 = _
      rw [Nat.mod_eq_of_lt (by omega)]
    have dominatesLeft : word.toNat ≤ (word ||| (-word)).toNat := by
      rw [UInt32.toNat_or]
      exact Nat.left_le_or
    have dominatesRight : (-word).toNat ≤ (word ||| (-word)).toNat := by
      rw [UInt32.toNat_or]
      exact Nat.right_le_or
    have high : 2147483648 ≤ (word ||| (-word)).toNat := by
      by_cases low : word.toNat < 2147483648
      · rw [negated] at dominatesRight
        omega
      · omega
    have upper : (word ||| (-word)).toNat < 4294967296 := (word ||| (-word)).toNat_lt
    rw [if_neg zero]
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change (word ||| (-word)).toNat / 2147483648 = 1
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

def sourceU32CtEqByte (a b : UInt32) : UInt8 :=
  UInt8.ofNat ((((a ^^^ b) ||| (-(a ^^^ b))) >>> 31) ^^^ 1).toNat

theorem source_u32_ct_equality_is_exact (a b : UInt32) :
    sourceU32CtEqByte a b = if a == b then 1 else 0 := by
  rw [sourceU32CtEqByte, source_u32_high_bit_detects_nonzero]
  by_cases same : a = b
  · simp [same]
  · simp [UInt32.xor_eq_zero_iff, same]

def sourceU32EqChoice (a b : UInt32) : SourceChoiceByte :=
  ⟨sourceU32CtEqByte a b, by rw [source_u32_ct_equality_is_exact]; split <;> decide⟩

def sourceU32Select (a b : UInt32) (choice : SourceChoiceByte) : UInt32 :=
  a ^^^ (-(UInt32.ofNat choice.byte.toNat) &&& (a ^^^ b))

theorem source_u32_masked_selection_is_exact (a b : UInt32) (choice : SourceChoiceByte) :
    sourceU32Select a b choice = if choice.byte = 0 then a else b := by
  rcases valid_source_choice_byte_is_exactly_zero_or_one choice with zero | one
  · simp [sourceU32Select, zero]
  · simp [sourceU32Select, one, ← UInt32.xor_assoc]

def sourceScalarEqChoice (a b : CanonicalScalar) : SourceChoiceByte :=
  ⟨sourceScalarWordsCtEqByte a.words b.words,
    TransferScalarPredicates01.source_scalar_equality_choice_byte_has_derived_bit_invariant _ _⟩

def sourceNotChoice (choice : SourceChoiceByte) : SourceChoiceByte :=
  ⟨sourceNotChoiceByte choice.byte, by
    rcases valid_source_choice_byte_is_exactly_zero_or_one choice with zero | one
    · rw [zero, sourceNotChoiceByte]; decide
    · rw [one, sourceNotChoiceByte]; decide⟩

def sourceAndChoice (a b : SourceChoiceByte) : SourceChoiceByte :=
  ⟨a.byte &&& b.byte, by
    rcases valid_source_choice_byte_is_exactly_zero_or_one a with zero | one <;>
      rcases valid_source_choice_byte_is_exactly_zero_or_one b with zero' | one'
    · rw [zero, zero']; decide
    · rw [zero, one']; decide
    · rw [one, zero']; decide
    · rw [one, one']; decide⟩

theorem source_scalar_choice_equality_is_exact (a b : CanonicalScalar) :
    (sourceScalarEqChoice a b).byte = if a.words = b.words then 1 else 0 := by
  exact TransferScalarConstantEquality01.exact_source_scalar_equality_byte_derives_exact_raw_word_equality _ _

set_option pp.all true in
#check @source_u32_high_bit_detects_nonzero
#print axioms source_u32_high_bit_detects_nonzero
set_option pp.all true in
#check @sourceU32CtEqByte
#print axioms sourceU32CtEqByte
set_option pp.all true in
#check @source_u32_ct_equality_is_exact
#print axioms source_u32_ct_equality_is_exact
set_option pp.all true in
#check @sourceU32EqChoice
#print axioms sourceU32EqChoice
set_option pp.all true in
#check @sourceU32Select
#print axioms sourceU32Select
set_option pp.all true in
#check @source_u32_masked_selection_is_exact
#print axioms source_u32_masked_selection_is_exact
set_option pp.all true in
#check @sourceScalarEqChoice
#print axioms sourceScalarEqChoice
set_option pp.all true in
#check @sourceNotChoice
#print axioms sourceNotChoice
set_option pp.all true in
#check @sourceAndChoice
#print axioms sourceAndChoice
set_option pp.all true in
#check @source_scalar_choice_equality_is_exact
#print axioms source_scalar_choice_equality_is_exact
end ShielddSecurity.TransferSqrtLoopPrimitives01
