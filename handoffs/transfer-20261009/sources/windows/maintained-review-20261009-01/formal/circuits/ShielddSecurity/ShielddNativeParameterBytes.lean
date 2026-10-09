import ShielddSecurity.ShielddNativePoseidonParameters

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativeParameterBytes

open GroupByteCodec

/- The pinned Poseidon field wrapper decodes a hex string, requires exactly
32 bytes, reverses that BE buffer, and calls encoding::field. The global hex
decoder below describes all rendered canonical integers. Its implementation
contract remains separate from these owned byte and Option sequences. -/

def bigEndianBuffer (value : Nat) : Bytes := fun index =>
  ⟨GroupScalarCodec.bigEndianByte value index.val, Nat.mod_lt _ (by decide)⟩

theorem reverse_bytes_twice (bytes : Bytes) :
    reverseBytes (reverseBytes bytes) = bytes := by
  funext index
  have offset : 31 - (31 - index.val) = index.val := by
    have := index.isLt
    omega
  simp only [reverseBytes, offset]

theorem reversed_big_endian (value : Nat) :
    reverseBytes (bigEndianBuffer value) =
      ShielddNativePoseidonParameters.sourceBuffer value := by
  funext index
  have offset : 31 - (31 - index.val) = index.val := by
    have := index.isLt
    omega
  simp only [reverseBytes, bigEndianBuffer,
    ShielddNativePoseidonParameters.sourceBuffer,
    GroupScalarCodec.bigEndianByte, littleEndianByte, offset]

def fixedBuffer (bytes : List Byte) : Option Bytes :=
  if length : bytes.length = 32 then
    some (fun index => bytes.get ⟨index.val, by rw [length]; exact index.isLt⟩)
  else none

theorem fixed_buffer_roundtrip (bytes : Bytes) :
    fixedBuffer (List.ofFn bytes) = some bytes := by
  have length : (List.ofFn bytes).length = 32 := by simp
  simp only [fixedBuffer, dif_pos length]
  apply congrArg Option.some
  funext index
  simp only [List.get_eq_getElem, List.getElem_ofFn]

structure HexCodec (Encoded : Type) where
  render : Nat → Encoded
  decode : Encoded → Option (List Byte)
  canonical : ∀ value : Nat, value < Scalar.modulus →
    decode (render value) = some (List.ofFn (bigEndianBuffer value))

def fieldBody {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (encoded : Encoded) : Option Q := do
  let bytes ← hex.decode encoded
  let buffer ← fixedBuffer bytes
  fq.parse (reverseBytes buffer)

theorem field_body_success {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (value : Nat)
    (bounded : value < Scalar.modulus) :
    ∃ native, fieldBody hex fq (hex.render value) = some native ∧
      fq.integer native = value := by
  obtain ⟨native, parsed, integer⟩ := fq.canonical value bounded
    (ShielddNativePoseidonParameters.sourceBuffer value) (fun _ => rfl)
  refine ⟨native, ?_, integer⟩
  change (hex.decode (hex.render value)).bind (fun bytes =>
    (fixedBuffer bytes).bind (fun buffer => fq.parse (reverseBytes buffer))) = some native
  rw [hex.canonical value bounded]
  change (fixedBuffer (List.ofFn (bigEndianBuffer value))).bind
    (fun buffer => fq.parse (reverseBytes buffer)) = some native
  rw [fixed_buffer_roundtrip]
  change fq.parse (reverseBytes (bigEndianBuffer value)) = some native
  rw [reversed_big_endian, parsed]

theorem field_body_integer {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (value : Nat)
    (bounded : value < Scalar.modulus) (native : Q)
    (decoded : fieldBody hex fq (hex.render value) = some native) :
    fq.integer native = value := by
  obtain ⟨expected, successful, integer⟩ := field_body_success hex fq value bounded
  have same : expected = native := Option.some.inj (successful.symm.trans decoded)
  exact same ▸ integer

set_option pp.all true in
#check @reverse_bytes_twice
#print axioms reverse_bytes_twice
set_option pp.all true in
#check @reversed_big_endian
#print axioms reversed_big_endian
set_option pp.all true in
#check @fixed_buffer_roundtrip
#print axioms fixed_buffer_roundtrip
set_option pp.all true in
#check @field_body_success
#print axioms field_body_success
set_option pp.all true in
#check @field_body_integer
#print axioms field_body_integer
end ShielddSecurity.ShielddNativeParameterBytes
