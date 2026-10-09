import ShielddSecurity.ShielddHexByteOperations
import ShielddSecurity.ShielddHexSourceSequence

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexJsonByteGuards

/- Literal serde_json 1.0.151 read.rs::is_escape(validate=true) and the
single-byte projections of its control/quote/backslash SWAR detectors.
These facts do not assume that the full native word scanner returns a
particular position or that Artifact deserialization succeeds. -/
def isEscape (code : Nat) : Bool := code == 34 || code == 92 || decide (code < 32)

def detectorByte (byte : UInt8) : UInt8 :=
  let control := (byte - 32) &&& (~~~byte)
  let quote := byte ^^^ 34
  let slash := byte ^^^ 92
  (control ||| ((quote - 1) &&& (~~~quote)) |||
    ((slash - 1) &&& (~~~slash))) &&& 128

theorem lower_digit_guard : ∀ index : Fin 16,
    32 ≤ ShielddHexCodec.lowerDigit index.val ∧
    ShielddHexCodec.lowerDigit index.val < 128 ∧
    isEscape (ShielddHexCodec.lowerDigit index.val) = false := by decide

theorem lower_digit_detector : ∀ index : Fin 16,
    detectorByte (UInt8.ofNat (ShielddHexCodec.lowerDigit index.val)) = 0 := by decide

theorem lower_digit_no_borrow : ∀ index : Fin 16,
    let byte := UInt8.ofNat (ShielddHexCodec.lowerDigit index.val)
    32 ≤ byte.toNat ∧ 0 < (byte ^^^ 34).toNat ∧ 0 < (byte ^^^ 92).toNat := by decide

theorem encoded_no_escape (bytes : List GroupByteCodec.Byte) :
    ∀ code ∈ ShielddHexCodec.encode bytes, isEscape code = false := by
  induction bytes with
  | nil => intro code member; simp only [ShielddHexCodec.encode, List.not_mem_nil] at member
  | cons byte rest ih =>
    intro code member
    simp only [ShielddHexCodec.encode, List.mem_cons] at member
    rcases member with same | same | member
    · subst code
      have bound : byte.val / 16 < 16 := by have := byte.isLt; omega
      exact (lower_digit_guard ⟨_, bound⟩).2.2
    · subst code
      exact (lower_digit_guard ⟨_, Nat.mod_lt _ (by decide)⟩).2.2
    · exact ih code member

def packed : List Nat → Nat
  | [] => 0
  | byte :: rest => byte + 256 * packed rest

def oneBytes : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + 256 * oneBytes n

/- The SWAR source subtracts repeated 0x20/0x01 bytes. This global arithmetic
recurrence establishes no inter-byte borrow when each digit admits the
subtraction. Fixed-word wrapping and bit-mask/first-hit correspondence remain
separate owned source obligations. -/
theorem packed_decomposition (bytes : List Nat) (amount : Nat)
    (enough : ∀ byte ∈ bytes, amount ≤ byte) :
    packed bytes = packed (bytes.map (fun byte => byte - amount)) +
      amount * oneBytes bytes.length := by
  induction bytes with
  | nil => simp only [packed, List.map_nil, List.length_nil, oneBytes, Nat.mul_zero, Nat.add_zero]
  | cons byte rest ih =>
    have head := enough byte (List.mem_cons_self)
    have tail : ∀ entry ∈ rest, amount ≤ entry := by
      intro entry member
      exact enough entry (List.mem_cons_of_mem byte member)
    have splitByte := Nat.sub_add_cancel head
    have splitRest := ih tail
    simp only [packed, List.map_cons, List.length_cons, oneBytes]
    rw [splitRest]
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
    rw [Nat.mul_left_comm 256 amount (oneBytes rest.length)]
    omega

theorem packed_subtraction (bytes : List Nat) (amount : Nat)
    (enough : ∀ byte ∈ bytes, amount ≤ byte) :
    packed bytes - amount * oneBytes bytes.length =
      packed (bytes.map (fun byte => byte - amount)) := by
  rw [packed_decomposition bytes amount enough]
  exact Nat.add_sub_cancel _ _

set_option pp.all true in
#check @lower_digit_guard
#print axioms lower_digit_guard
set_option pp.all true in
#check @lower_digit_detector
#print axioms lower_digit_detector
set_option pp.all true in
#check @lower_digit_no_borrow
#print axioms lower_digit_no_borrow
set_option pp.all true in
#check @encoded_no_escape
#print axioms encoded_no_escape
set_option pp.all true in
#check @packed_decomposition
#print axioms packed_decomposition
set_option pp.all true in
#check @packed_subtraction
#print axioms packed_subtraction

end ShielddSecurity.ShielddHexJsonByteGuards
