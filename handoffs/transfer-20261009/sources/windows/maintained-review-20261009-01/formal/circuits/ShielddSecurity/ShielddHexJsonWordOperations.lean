import ShielddSecurity.ShielddHexJsonByteGuards

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexJsonWordOperations

open ShielddHexJsonByteGuards

/- Symbolic packed-word operations used by the actual JSON ASCII scanner.
They are arithmetic/bitwise consequences, not a native scanner return law. -/
theorem byte_join_and (a b upperA upperB : Nat) (ha : a < 256) (hb : b < 256) :
    (a + 256 * upperA) &&& (b + 256 * upperB) =
      (a &&& b) + 256 * (upperA &&& upperB) := by
  have joined : a &&& b < 256 := lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.add_comm a (256 * upperA), Nat.add_comm b (256 * upperB),
    Nat.add_comm (a &&& b) (256 * (upperA &&& upperB))]
  change (2 ^ 8 * upperA + a) &&& (2 ^ 8 * upperB + b) =
    2 ^ 8 * (upperA &&& upperB) + (a &&& b)
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add upperA ha bit,
    Nat.testBit_two_pow_mul_add upperB hb bit,
    Nat.testBit_two_pow_mul_add (upperA &&& upperB) joined bit]
  by_cases low : bit < 8 <;> simp [low, Nat.testBit_and]

theorem byte_join_xor (a b upperA upperB : Nat) (ha : a < 256) (hb : b < 256) :
    (a + 256 * upperA) ^^^ (b + 256 * upperB) =
      (a ^^^ b) + 256 * (upperA ^^^ upperB) := by
  have joined : a ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) ha hb
  rw [Nat.add_comm a (256 * upperA), Nat.add_comm b (256 * upperB),
    Nat.add_comm (a ^^^ b) (256 * (upperA ^^^ upperB))]
  change (2 ^ 8 * upperA + a) ^^^ (2 ^ 8 * upperB + b) =
    2 ^ 8 * (upperA ^^^ upperB) + (a ^^^ b)
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add upperA ha bit,
    Nat.testBit_two_pow_mul_add upperB hb bit,
    Nat.testBit_two_pow_mul_add (upperA ^^^ upperB) joined bit]
  by_cases low : bit < 8 <;> simp [low, Nat.testBit_xor]

theorem packed_xor_constant (bytes : List Nat) (constant : Nat)
    (bound : constant < 256) (byteBounds : ∀ byte ∈ bytes, byte < 256) :
    packed bytes ^^^ (constant * oneBytes bytes.length) =
      packed (bytes.map (fun byte => byte ^^^ constant)) := by
  induction bytes with
  | nil => simp only [packed, oneBytes, List.length_nil, List.map_nil, Nat.mul_zero, Nat.xor_self]
  | cons byte rest ih =>
    have head := byteBounds byte (List.mem_cons_self)
    have tail : ∀ entry ∈ rest, entry < 256 := by
      intro entry member
      exact byteBounds entry (List.mem_cons_of_mem byte member)
    simp only [packed, List.map_cons, List.length_cons, oneBytes, Nat.mul_add, Nat.mul_one]
    rw [Nat.mul_left_comm constant 256 (oneBytes rest.length)]
    rw [byte_join_xor byte constant _ _ head bound, ih tail]

def highMask : Nat → Nat
  | 0 => 0
  | n + 1 => 128 + 256 * highMask n

theorem high_mask_repeated (length : Nat) : highMask length = 128 * oneBytes length := by
  induction length with
  | zero => rfl
  | succ n ih =>
    simp only [highMask, oneBytes, ih, Nat.mul_add, Nat.mul_one]
    rw [Nat.mul_left_comm 128 256 (oneBytes n)]

theorem packed_high_mask_zero (bytes : List Nat)
    (byteBounds : ∀ byte ∈ bytes, byte < 128) :
    packed bytes &&& highMask bytes.length = 0 := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have head := byteBounds byte (List.mem_cons_self)
    have byteBound : byte < 256 := by omega
    have tail : ∀ entry ∈ rest, entry < 128 := by
      intro entry member
      exact byteBounds entry (List.mem_cons_of_mem byte member)
    have localMask : byte &&& 128 = 0 :=
      (show ∀ index : Fin 128, index.val &&& 128 = 0 from by decide) ⟨byte, head⟩
    simp only [packed, highMask, List.length_cons]
    rw [byte_join_and byte 128 _ _ byteBound (by decide), localMask, ih tail]

theorem masked_subtraction_zero (bytes : List Nat) (amount complement : Nat)
    (enough : ∀ byte ∈ bytes, amount ≤ byte)
    (small : ∀ byte ∈ bytes, byte - amount < 128) :
    ((packed bytes - amount * oneBytes bytes.length) &&& complement) &&&
      highMask bytes.length = 0 := by
  have zero : (packed bytes - amount * oneBytes bytes.length) &&&
      highMask bytes.length = 0 := by
    rw [packed_subtraction bytes amount enough]
    have bounded : ∀ value ∈ bytes.map (fun byte => byte - amount), value < 128 := by
      intro value member
      obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
      exact small byte inBytes
    simpa only [List.length_map] using packed_high_mask_zero _ bounded
  rw [Nat.and_assoc, Nat.and_comm complement (highMask bytes.length), ← Nat.and_assoc, zero]
  exact Nat.zero_and _

set_option pp.all true in
#check @byte_join_and
#print axioms byte_join_and
set_option pp.all true in
#check @byte_join_xor
#print axioms byte_join_xor
set_option pp.all true in
#check @packed_xor_constant
#print axioms packed_xor_constant
set_option pp.all true in
#check @high_mask_repeated
#print axioms high_mask_repeated
set_option pp.all true in
#check @packed_high_mask_zero
#print axioms packed_high_mask_zero
set_option pp.all true in
#check @masked_subtraction_zero
#print axioms masked_subtraction_zero

end ShielddSecurity.ShielddHexJsonWordOperations
