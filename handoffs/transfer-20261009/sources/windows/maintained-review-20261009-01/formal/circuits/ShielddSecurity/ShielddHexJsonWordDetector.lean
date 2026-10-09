import ShielddSecurity.ShielddHexJsonWordOperations

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexJsonWordDetector

open ShielddHexJsonByteGuards ShielddHexJsonWordOperations

def SafeByte (byte : Nat) : Prop :=
  (32 ≤ byte ∧ byte < 128) ∧
  (1 ≤ byte ^^^ 34 ∧ byte ^^^ 34 < 128) ∧
  (1 ≤ byte ^^^ 92 ∧ byte ^^^ 92 < 128)

theorem lower_digit_conditions : ∀ index : Fin 16,
    SafeByte (ShielddHexCodec.lowerDigit index.val) := by
  unfold SafeByte
  decide

theorem encoded_conditions (bytes : List GroupByteCodec.Byte) :
    ∀ code ∈ ShielddHexCodec.encode bytes, SafeByte code := by
  induction bytes with
  | nil => intro code member; simp only [ShielddHexCodec.encode, List.not_mem_nil] at member
  | cons byte rest ih =>
    intro code member
    simp only [ShielddHexCodec.encode, List.mem_cons] at member
    rcases member with same | same | member
    · subst code
      have bound : byte.val / 16 < 16 := by have := byte.isLt; omega
      exact lower_digit_conditions ⟨_, bound⟩
    · subst code
      exact lower_digit_conditions ⟨_, Nat.mod_lt _ (by decide)⟩
    · exact ih code member

def complement (length value : Nat) : Nat := (2 ^ (8 * length) - 1) ^^^ value

/- Literal natural-number view of the native three detector expressions.
The theorem below establishes their zero mask algebraically. Its separate
source instantiation must bind actual bounded words, wrapping arithmetic,
little-endian byte reads and ONE_BYTES/highMask to this view. -/
def detector (bytes : List Nat) : Nat :=
  let chars := packed bytes
  let ones := oneBytes bytes.length
  let quote := chars ^^^ (34 * ones)
  let slash := chars ^^^ (92 * ones)
  (((chars - 32 * ones) &&& complement bytes.length chars) |||
    ((quote - ones) &&& complement bytes.length quote) |||
    ((slash - ones) &&& complement bytes.length slash)) &&& highMask bytes.length

theorem detector_zero (bytes : List Nat) (safe : ∀ byte ∈ bytes, SafeByte byte) :
    detector bytes = 0 := by
  have bounds : ∀ byte ∈ bytes, byte < 256 := by
    intro byte member
    have := (safe byte member).1.2
    omega
  have control : ((packed bytes - 32 * oneBytes bytes.length) &&&
      complement bytes.length (packed bytes)) &&& highMask bytes.length = 0 := by
    apply masked_subtraction_zero
    · intro byte member
      exact (safe byte member).1.1
    · intro byte member
      have := (safe byte member).1.2
      omega
  have quote : (((packed bytes ^^^ (34 * oneBytes bytes.length)) - oneBytes bytes.length) &&&
      complement bytes.length (packed bytes ^^^ (34 * oneBytes bytes.length))) &&&
      highMask bytes.length = 0 := by
    rw [packed_xor_constant bytes 34 (by decide) bounds]
    have enough : ∀ value ∈ bytes.map (fun byte => byte ^^^ 34), 1 ≤ value := by
      intro value member
      obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
      exact (safe byte inBytes).2.1.1
    have small : ∀ value ∈ bytes.map (fun byte => byte ^^^ 34), value - 1 < 128 := by
      intro value member
      obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
      have := (safe byte inBytes).2.1.2
      omega
    simpa only [List.length_map, Nat.one_mul] using
      (masked_subtraction_zero (bytes.map (fun byte => byte ^^^ 34)) 1
        (complement bytes.length (packed (bytes.map (fun byte => byte ^^^ 34)))) enough small)
  have slash : (((packed bytes ^^^ (92 * oneBytes bytes.length)) - oneBytes bytes.length) &&&
      complement bytes.length (packed bytes ^^^ (92 * oneBytes bytes.length))) &&&
      highMask bytes.length = 0 := by
    rw [packed_xor_constant bytes 92 (by decide) bounds]
    have enough : ∀ value ∈ bytes.map (fun byte => byte ^^^ 92), 1 ≤ value := by
      intro value member
      obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
      exact (safe byte inBytes).2.2.1
    have small : ∀ value ∈ bytes.map (fun byte => byte ^^^ 92), value - 1 < 128 := by
      intro value member
      obtain ⟨byte, inBytes, rfl⟩ := List.mem_map.mp member
      have := (safe byte inBytes).2.2.2
      omega
    simpa only [List.length_map, Nat.one_mul] using
      (masked_subtraction_zero (bytes.map (fun byte => byte ^^^ 92)) 1
        (complement bytes.length (packed (bytes.map (fun byte => byte ^^^ 92)))) enough small)
  unfold detector
  rw [Nat.and_or_distrib_right, Nat.and_or_distrib_right, control, quote, slash]
  simp only [Nat.or_zero]

theorem encoded_chunk_detector_zero (bytes : List GroupByteCodec.Byte) (chunk : List Nat)
    (members : ∀ code ∈ chunk, code ∈ ShielddHexCodec.encode bytes) :
    detector chunk = 0 := by
  apply detector_zero
  intro code member
  exact encoded_conditions bytes code (members code member)

set_option pp.all true in
#check @lower_digit_conditions
#print axioms lower_digit_conditions
set_option pp.all true in
#check @encoded_conditions
#print axioms encoded_conditions
set_option pp.all true in
#check @detector_zero
#print axioms detector_zero
set_option pp.all true in
#check @encoded_chunk_detector_zero
#print axioms encoded_chunk_detector_zero

end ShielddSecurity.ShielddHexJsonWordDetector
