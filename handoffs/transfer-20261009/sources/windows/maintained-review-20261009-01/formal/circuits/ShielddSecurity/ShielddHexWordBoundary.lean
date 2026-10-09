import ShielddSecurity.ShielddHexJsonWordOperations

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexWordBoundary

open ShielddHexJsonByteGuards

/- Word-sized boundary algebra for the actual last coefficient word: seven
plain bytes followed by its closing quote. Universal recurrences here derive
byte packing/no-borrow and wrap behavior; no source scan answer is an input. -/
theorem block_join_and (bits a b upperA upperB : Nat)
    (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    (a + 2 ^ bits * upperA) &&& (b + 2 ^ bits * upperB) =
      (a &&& b) + 2 ^ bits * (upperA &&& upperB) := by
  have joined : a &&& b < 2 ^ bits := lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.add_comm a (2 ^ bits * upperA), Nat.add_comm b (2 ^ bits * upperB),
    Nat.add_comm (a &&& b) (2 ^ bits * (upperA &&& upperB))]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add upperA ha bit,
    Nat.testBit_two_pow_mul_add upperB hb bit,
    Nat.testBit_two_pow_mul_add (upperA &&& upperB) joined bit]
  by_cases low : bit < bits <;> simp [low, Nat.testBit_and]

theorem block_join_xor (bits a b upperA upperB : Nat)
    (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    (a + 2 ^ bits * upperA) ^^^ (b + 2 ^ bits * upperB) =
      (a ^^^ b) + 2 ^ bits * (upperA ^^^ upperB) := by
  have joined : a ^^^ b < 2 ^ bits := Nat.xor_lt_two_pow ha hb
  rw [Nat.add_comm a (2 ^ bits * upperA), Nat.add_comm b (2 ^ bits * upperB),
    Nat.add_comm (a ^^^ b) (2 ^ bits * (upperA ^^^ upperB))]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add upperA ha bit,
    Nat.testBit_two_pow_mul_add upperB hb bit,
    Nat.testBit_two_pow_mul_add (upperA ^^^ upperB) joined bit]
  by_cases low : bit < bits <;> simp [low, Nat.testBit_xor]

theorem packed_append (before after : List Nat) :
    packed (before ++ after) = packed before + 256 ^ before.length * packed after := by
  induction before with
  | nil => simp [packed]
  | cons byte rest ih =>
    simp only [List.cons_append, packed, List.length_cons, ih, Nat.pow_succ]
    ring

theorem packed_bound (bytes : List Nat) (bounds : ∀ byte ∈ bytes, byte < 256) :
    packed bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons byte rest ih =>
    have head := bounds byte (List.mem_cons_self)
    have tail := ih (fun entry member => bounds entry (List.mem_cons_of_mem byte member))
    simp only [packed, List.length_cons, Nat.pow_succ]
    omega

theorem packed_enough (bytes : List Nat) (amount : Nat)
    (enough : ∀ byte ∈ bytes, amount ≤ byte) :
    amount * oneBytes bytes.length ≤ packed bytes := by
  induction bytes with
  | nil => simp [packed, oneBytes]
  | cons byte rest ih =>
    have head := enough byte (List.mem_cons_self)
    have tail := ih (fun entry member => enough entry (List.mem_cons_of_mem byte member))
    change amount * (1 + 256 * oneBytes rest.length) ≤ byte + 256 * packed rest
    calc
      amount * (1 + 256 * oneBytes rest.length) =
          amount + 256 * (amount * oneBytes rest.length) := by ring
      _ ≤ byte + 256 * packed rest := Nat.add_le_add head (Nat.mul_le_mul_left 256 tail)

def wrappedSub (modulus value amount : Nat) : Nat := (value + modulus - amount) % modulus

theorem wrapped_no_borrow (modulus value amount : Nat)
    (enough : amount ≤ value) (bound : value < modulus) :
    wrappedSub modulus value amount = value - amount := by
  have arranged : value + modulus - amount = modulus + (value - amount) := by omega
  have resultBound : value - amount < modulus := by omega
  simp [wrappedSub, arranged, Nat.mod_eq_of_lt resultBound]

/- Actual ONE_BYTES for eight bytes exceeds the 56-bit leading by ONE_BYTES
for its seven low bytes. The zero high byte of chars XOR repeated quote
therefore wraps to high byte255 and leaves the exact low subtraction. -/
theorem wrapped_closing_quote (leading : Nat)
    (enough : oneBytes 7 ≤ leading) (bound : leading < 2 ^ 56) :
    wrappedSub (2 ^ 64) leading (oneBytes 8) =
      (leading - oneBytes 7) + 2 ^ 56 * 255 := by
  change 282578800148737 ≤ leading at enough
  change leading < 72057594037927936 at bound
  change (leading + 18446744073709551616 - 72340172838076673) %
      18446744073709551616 = leading - 282578800148737 + 18374686479671623680
  have arranged : leading + 18446744073709551616 - 72340172838076673 =
      leading - 282578800148737 + 18374686479671623680 := by omega
  have resultBound : leading - 282578800148737 + 18374686479671623680 <
      18446744073709551616 := by omega
  rw [arranged, Nat.mod_eq_of_lt resultBound]

/- Independent bounded recurrence for the Rust cttz primitive's functional
operation. Instantiation with actual UInt64/intrinsics still has a source
obligation; the selected closing mask and byte index are derived constants. -/
def trailingBits : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, value => if value % 2 = 1 then 0 else 1 + trailingBits fuel (value / 2)

theorem closing_mask_position : trailingBits 64 (2 ^ 63) / 8 = 7 := by decide

set_option pp.all true in
#check @block_join_and
#print axioms block_join_and
set_option pp.all true in
#check @block_join_xor
#print axioms block_join_xor
set_option pp.all true in
#check @packed_append
#print axioms packed_append
set_option pp.all true in
#check @packed_bound
#print axioms packed_bound
set_option pp.all true in
#check @packed_enough
#print axioms packed_enough
set_option pp.all true in
#check @wrapped_no_borrow
#print axioms wrapped_no_borrow
set_option pp.all true in
#check @wrapped_closing_quote
#print axioms wrapped_closing_quote
set_option pp.all true in
#check @closing_mask_position
#print axioms closing_mask_position

end ShielddSecurity.ShielddHexWordBoundary
