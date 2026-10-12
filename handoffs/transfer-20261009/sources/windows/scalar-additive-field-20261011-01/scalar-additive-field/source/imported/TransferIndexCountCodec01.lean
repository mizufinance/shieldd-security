import ShielddSecurity.TransferOrdinaryIndexCountSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferIndexCountCodec01

open TransferStateDelta TransferIndexWriterModel01

/-! Big-endian u64 count codec, using symbolic width recurrences. Abstract Nat
bytes are checked for range; real Vec<u8> representation supplies that range.
The pinned Rust accepts exactly eight bytes, defaults absence to zero, and
writes u64.to_be_bytes. Rust/Lean byte conversion remains a source interface. -/

def encodeBE : Nat → Nat → Bytes
  | 0, _ => []
  | width + 1, value => value / 256 ^ width :: encodeBE width (value % 256 ^ width)

def decodeBE : Bytes → Nat
  | [] => 0
  | byte :: rest => byte * 256 ^ rest.length + decodeBE rest

def validBytes (bytes : Bytes) : Bool := bytes.all (fun byte => decide (byte < 256))

def decodeCount (bytes : Bytes) : Option Ordinal :=
  if safe : bytes.length = 8 ∧ validBytes bytes = true ∧ decodeBE bytes < 2 ^ 64 then
    some ⟨decodeBE bytes, safe.2.2⟩ else none

def codec : Codec := ⟨decodeCount, fun ordinal => encodeBE 8 ordinal.val⟩

theorem encode_length (width value : Nat) : (encodeBE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [encodeBE, List.length_cons, ih]

theorem encode_valid (width value : Nat) (bounded : value < 256 ^ width) :
    validBytes (encodeBE width value) = true := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    have byteBound : value / 256 ^ width < 256 :=
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 256))).mpr
        (by simpa only [Nat.pow_succ'] using bounded)
    have tailBound : value % 256 ^ width < 256 ^ width :=
      Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 256))
    simp only [encodeBE, validBytes, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨byteBound, ih _ tailBound⟩

theorem decode_valid_bound (bytes : Bytes) (valid : validBytes bytes = true) :
    decodeBE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons byte rest ih =>
    have parts : byte < 256 ∧ validBytes rest = true := by
      simpa only [validBytes, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] using valid
    have tailBound := ih parts.2
    calc
      decodeBE (byte :: rest) = byte * 256 ^ rest.length + decodeBE rest := rfl
      _ < byte * 256 ^ rest.length + 256 ^ rest.length := Nat.add_lt_add_left tailBound _
      _ = (byte + 1) * 256 ^ rest.length := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 256 * 256 ^ rest.length := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt parts.1)
      _ = 256 ^ (byte :: rest).length := by simp only [List.length_cons, Nat.pow_succ']

theorem decode_encode (width value : Nat) (bounded : value < 256 ^ width) :
    decodeBE (encodeBE width value) = value := by
  induction width generalizing value with
  | zero =>
    have zero : value = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bounded)
    subst value
    rfl
  | succ width ih =>
    have tailBound : value % 256 ^ width < 256 ^ width :=
      Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 256))
    simp only [encodeBE, decodeBE, encode_length, ih _ tailBound]
    exact Nat.div_add_mod' value (256 ^ width)

theorem decode_success_iff (bytes : Bytes) (ordinal : Ordinal) :
    decodeCount bytes = some ordinal ↔
      bytes.length = 8 ∧ validBytes bytes = true ∧ decodeBE bytes = ordinal.val := by
  unfold decodeCount
  split
  next safe =>
    constructor
    · intro same
      exact ⟨safe.1, safe.2.1, congrArg Fin.val (Option.some.inj same)⟩
    · intro same
      exact congrArg some (Fin.ext same.2.2)
  next rejected =>
    constructor
    · intro impossible
      contradiction
    · intro same
      exact False.elim (rejected ⟨same.1, same.2.1, same.2.2 ▸ ordinal.isLt⟩)

theorem codec_roundtrip (ordinal : Ordinal) :
    codec.decodeCount (codec.encodeCount ordinal) = some ordinal := by
  apply (decode_success_iff _ ordinal).mpr
  have bounded : ordinal.val < 256 ^ 8 := ordinal.isLt
  exact ⟨encode_length 8 ordinal.val, encode_valid 8 ordinal.val bounded, decode_encode 8 ordinal.val bounded⟩

theorem malformed_iff_wrong_length_for_real_bytes (bytes : Bytes)
    (valid : validBytes bytes = true) : decodeCount bytes = none ↔ bytes.length ≠ 8 := by
  unfold decodeCount
  split
  next safe =>
    constructor
    · intro impossible
      contradiction
    · intro wrong
      exact False.elim (wrong safe.1)
  next rejected =>
    constructor
    · intro _ sized
      have bounded := decode_valid_bound bytes valid
      rw [sized] at bounded
      exact rejected ⟨sized, valid, bounded⟩
    · intro _
      rfl

theorem absent_count_is_zero : countObservation codec none = some ⟨0, by decide⟩ := rfl

theorem wrong_length_is_invalid_count (bytes : Bytes) (wrong : bytes.length ≠ 8) :
    countObservation codec (some bytes) = none := by
  change decodeCount bytes = none
  have rejected : ¬ (bytes.length = 8 ∧ validBytes bytes = true ∧ decodeBE bytes < 2 ^ 64) := fun safe => wrong safe.1
  simp only [decodeCount, dif_neg rejected]

theorem decoded_full_count_refuses_increment :
    nextOrdinal (⟨2 ^ 64 - 1, by decide⟩ : Ordinal) = none := by
  exact nextOrdinal_overflow _ (by decide)

set_option pp.all true in
#check @encodeBE
#print axioms encodeBE
set_option pp.all true in
#check @decodeBE
#print axioms decodeBE
set_option pp.all true in
#check @validBytes
#print axioms validBytes
set_option pp.all true in
#check @decodeCount
#print axioms decodeCount
set_option pp.all true in
#check @codec
#print axioms codec
set_option pp.all true in
#check @encode_length
#print axioms encode_length
set_option pp.all true in
#check @encode_valid
#print axioms encode_valid
set_option pp.all true in
#check @decode_valid_bound
#print axioms decode_valid_bound
set_option pp.all true in
#check @decode_encode
#print axioms decode_encode
set_option pp.all true in
#check @decode_success_iff
#print axioms decode_success_iff
set_option pp.all true in
#check @codec_roundtrip
#print axioms codec_roundtrip
set_option pp.all true in
#check @malformed_iff_wrong_length_for_real_bytes
#print axioms malformed_iff_wrong_length_for_real_bytes
set_option pp.all true in
#check @absent_count_is_zero
#print axioms absent_count_is_zero
set_option pp.all true in
#check @wrong_length_is_invalid_count
#print axioms wrong_length_is_invalid_count
set_option pp.all true in
#check @decoded_full_count_refuses_increment
#print axioms decoded_full_count_refuses_increment

end ShielddSecurity.TransferIndexCountCodec01
