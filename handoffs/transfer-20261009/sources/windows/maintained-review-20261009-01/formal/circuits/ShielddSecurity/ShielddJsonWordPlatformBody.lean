import ShielddSecurity.ShielddHexChunkSource

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddJsonWordPlatformBody

open ShielddHexJsonByteGuards ShielddHexJsonWordOperations
open ShielddHexWordBoundary ShielddHexClosingQuoteWord

abbrev WordBytes := Fin 8 → GroupByteCodec.Byte

/- Separate standard machine primitives, universally over their operands.
No operation below describes serde, an owned scanner return, a coefficient,
or an accepted transaction. Actual compiler/platform instantiation and valid
memory views remain visible source obligations. In particular the source
from_le_bytes/transmute and cttz calls are not replaced by a whole Rust ABI. -/
structure Primitives (Word : Type) where
  value : Word → Nat
  constant : Nat → Word
  readLE8 : WordBytes → Word
  wrappingSub : Word → Word → Word
  bitAnd : Word → Word → Word
  bitOr : Word → Word → Word
  bitXor : Word → Word → Word
  bitNot : Word → Word
  trailingZeros : Word → Nat
  constant_value : ∀ n, value (constant n) = n % 2 ^ 64
  read_value : ∀ bytes, value (readLE8 bytes) = packed (List.ofFn (fun i => (bytes i).val))
  sub_value : ∀ a b, value (wrappingSub a b) =
    (value a + 2 ^ 64 - value b) % 2 ^ 64
  and_value : ∀ a b, value (bitAnd a b) = value a &&& value b
  or_value : ∀ a b, value (bitOr a b) = value a ||| value b
  xor_value : ∀ a b, value (bitXor a b) = value a ^^^ value b
  not_value : ∀ a, value (bitNot a) = (2 ^ 64 - 1) ^^^ value a
  trailing_value : ∀ a, value a ≠ 0 → trailingZeros a = trailingBits 64 (value a)

/- Literal read.rs body after the successful eight-byte array conversion.
Multiplication/shift of ONE_BYTES are compile-time constants, independently
checked by source_constants; the three subtractions still wrap at64 bits. -/
def sourceMask {Word : Type} (p : Primitives Word) (bytes : WordBytes) : Word :=
  let chars := p.readLE8 bytes
  let containsCtrl := p.bitAnd
    (p.wrappingSub chars (p.constant (32 * oneBytes 8))) (p.bitNot chars)
  let quote := p.bitXor chars (p.constant (34 * oneBytes 8))
  let containsQuote := p.bitAnd
    (p.wrappingSub quote (p.constant (oneBytes 8))) (p.bitNot quote)
  let slash := p.bitXor chars (p.constant (92 * oneBytes 8))
  let containsSlash := p.bitAnd
    (p.wrappingSub slash (p.constant (oneBytes 8))) (p.bitNot slash)
  p.bitAnd (p.bitOr (p.bitOr containsCtrl containsQuote) containsSlash)
    (p.constant (128 * oneBytes 8))

theorem source_constants :
    (2 ^ 64 - 1) / 255 = oneBytes 8 ∧
    (oneBytes 8 <<< 7) = highMask 8 ∧
    32 * oneBytes 8 < 2 ^ 64 ∧ 34 * oneBytes 8 < 2 ^ 64 ∧
    92 * oneBytes 8 < 2 ^ 64 ∧ 128 * oneBytes 8 < 2 ^ 64 := by decide

theorem word_body_value {Word : Type} (p : Primitives Word) (bytes : WordBytes) :
    p.value (sourceMask p bytes) = wordMask (List.ofFn (fun i => (bytes i).val)) := by
  have one : oneBytes 8 < 2 ^ 64 := by decide
  obtain ⟨_, _, ctrl, quote, slash, high⟩ := source_constants
  unfold sourceMask wordMask ShielddHexJsonWordDetector.complement
  simp only [p.and_value, p.or_value, p.sub_value, p.not_value, p.xor_value,
    p.read_value, p.constant_value, Nat.mod_eq_of_lt ctrl,
    Nat.mod_eq_of_lt quote, Nat.mod_eq_of_lt slash, Nat.mod_eq_of_lt high,
    Nat.mod_eq_of_lt one, high_mask_repeated, wrappedSub]

/- One native for-loop branch, with the chunk start already viewed as its
same-allocation byte offset. None means continue to the next word, never
whole JSON rejection. Pointer safety and bounded usize arithmetic are not
inferred merely from this natural-number operational model. -/
def sourceStep {Word : Type} (p : Primitives Word) (chunkStart : Nat)
    (bytes : WordBytes) : Option Nat :=
  let mask := sourceMask p bytes
  if p.value mask = 0 then none
  else some (chunkStart + p.trailingZeros mask / 8)

theorem word_branch {Word : Type} (p : Primitives Word) (chunkStart : Nat)
    (bytes : WordBytes) :
    sourceStep p chunkStart bytes =
      if wordMask (List.ofFn (fun i => (bytes i).val)) = 0 then none
      else some (chunkStart + trailingBits 64
        (wordMask (List.ofFn (fun i => (bytes i).val))) / 8) := by
  by_cases zero : p.value (sourceMask p bytes) = 0
  · have viewed : wordMask (List.ofFn (fun i => (bytes i).val)) = 0 :=
      (word_body_value p bytes).symm.trans zero
    simp only [sourceStep, if_pos zero, if_pos viewed]
  · have trailing := p.trailing_value (sourceMask p bytes) zero
    rw [word_body_value] at zero trailing
    simp only [sourceStep, word_body_value, if_neg zero, trailing]

set_option pp.all true in
#check @source_constants
#print axioms source_constants
set_option pp.all true in
#check @word_body_value
#print axioms word_body_value
set_option pp.all true in
#check @word_branch
#print axioms word_branch

end ShielddSecurity.ShielddJsonWordPlatformBody
