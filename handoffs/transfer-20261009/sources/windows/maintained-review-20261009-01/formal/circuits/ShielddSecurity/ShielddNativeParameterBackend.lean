import ShielddSecurity.NativeAssetHashParameters

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativeParameterBackend

/- This conditional wrapper contract concerns every byte list. It describes
no chosen coefficient, loaded table, asset hash or Transfer consequence. The
concrete Rust hex::decode / lowercase-encoding instance remains an open source
correspondence obligation. It is not supplied by the user's allowed
Pari/Commonware/curve assumptions. These consequences do not prove that
external roundtrip, Rust serde, iterator behavior or a native codec instance. -/
structure HexBackend (Encoded : Type) where
  encode : List GroupByteCodec.Byte → Encoded
  decode : Encoded → Option (List GroupByteCodec.Byte)
  roundtrip : ∀ bytes, decode (encode bytes) = some bytes

def hexCodec {Encoded : Type} (backend : HexBackend Encoded) :
    ShielddNativeParameterBytes.HexCodec Encoded where
  render := fun value => backend.encode
    (List.ofFn (ShielddNativeParameterBytes.bigEndianBuffer value))
  decode := backend.decode
  canonical := fun value _ => backend.roundtrip _

theorem hex_instance {Encoded : Type} (backend : HexBackend Encoded) (value : Nat) :
    (hexCodec backend).decode ((hexCodec backend).render value) =
      some (List.ofFn (ShielddNativeParameterBytes.bigEndianBuffer value)) :=
  backend.roundtrip _

/- The owned field wrapper first checks32 bytes and then reverses them. This
equality holds for any actual32-byte value, including a noncanonical Fq input:
rejection remains exactly the upstream parse result, not forced success. -/
theorem field_encoded_bytes {Encoded Q : Type} (backend : HexBackend Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (bytes : GroupByteCodec.Bytes) :
    ShielddNativeParameterBytes.fieldBody (hexCodec backend) fq
      (backend.encode (List.ofFn bytes)) =
      fq.parse (GroupByteCodec.reverseBytes bytes) := by
  change (backend.decode (backend.encode (List.ofFn bytes))).bind (fun decoded =>
    (ShielddNativeParameterBytes.fixedBuffer decoded).bind (fun buffer =>
      fq.parse (GroupByteCodec.reverseBytes buffer))) = _
  rw [backend.roundtrip]
  change (ShielddNativeParameterBytes.fixedBuffer (List.ofFn bytes)).bind
    (fun buffer => fq.parse (GroupByteCodec.reverseBytes buffer)) = _
  rw [ShielddNativeParameterBytes.fixed_buffer_roundtrip]
  rfl

theorem field_canonical_integer {Encoded Q : Type} (backend : HexBackend Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (value : Nat)
    (bounded : value < Scalar.modulus) :
    ∃ native, ShielddNativeParameterBytes.fieldBody (hexCodec backend) fq
      ((hexCodec backend).render value) = some native ∧ fq.integer native = value :=
  ShielddNativeParameterBytes.field_body_success (hexCodec backend) fq value bounded

theorem asset_hash_from_backend {F Q Encoded : Type} [Field F] [CharP F Scalar.modulus]
    (backend : HexBackend Encoded) (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F) (asset : Q) :
    (NativeAssetHashParameters.assetSource (hexCodec backend) fq arithmetic initial square asset).map
      (fun value => (fq.integer value : F)) =
      some (Poseidon.hash3 NativeAssetHashParameters.smallParameters 26 [(fq.integer asset : F)]) :=
  NativeAssetHashParameters.asset_source_value (hexCodec backend) fq arithmetic initial square codec asset

set_option pp.all true in
#check @hex_instance
#print axioms hex_instance
set_option pp.all true in
#check @field_encoded_bytes
#print axioms field_encoded_bytes
set_option pp.all true in
#check @field_canonical_integer
#print axioms field_canonical_integer
set_option pp.all true in
#check @asset_hash_from_backend
#print axioms asset_hash_from_backend

end ShielddSecurity.ShielddNativeParameterBackend
