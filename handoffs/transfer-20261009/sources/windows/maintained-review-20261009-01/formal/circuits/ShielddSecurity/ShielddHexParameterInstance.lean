import ShielddSecurity.ShielddHexCodec
import ShielddSecurity.ShielddNativeParameterBackend

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexParameterInstance

/- The byte-list source view has a constructed backend: the global roundtrip
is proved from the concrete nibble and pair algorithms. It is not an assumed
hex contract. Rust String/ASCII/iterator and Result-error source correspondence
remain visible in the companion source review; no Rust theorem is claimed. -/
def backend : ShielddNativeParameterBackend.HexBackend (List Nat) where
  encode := ShielddHexCodec.encode
  decode := ShielddHexCodec.decode
  roundtrip := ShielddHexCodec.decode_encoded

theorem hex_backend (bytes : List GroupByteCodec.Byte) :
    backend.decode (backend.encode bytes) = some bytes :=
  ShielddHexCodec.decode_encoded bytes

theorem field_buffer {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (bytes : GroupByteCodec.Bytes) :
    ShielddNativeParameterBytes.fieldBody
      (ShielddNativeParameterBackend.hexCodec backend) fq
      (ShielddHexCodec.encode (List.ofFn bytes)) =
      fq.parse (GroupByteCodec.reverseBytes bytes) :=
  ShielddNativeParameterBackend.field_encoded_bytes backend fq bytes

theorem field_wrong_length {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (bytes : List GroupByteCodec.Byte) (wrong : bytes.length ≠ 32) :
    ShielddNativeParameterBytes.fieldBody
      (ShielddNativeParameterBackend.hexCodec backend) fq
      (ShielddHexCodec.encode bytes) = none := by
  change (ShielddHexCodec.decode (ShielddHexCodec.encode bytes)).bind
    (fun decoded => (ShielddNativeParameterBytes.fixedBuffer decoded).bind
      (fun buffer => fq.parse (GroupByteCodec.reverseBytes buffer))) = none
  rw [ShielddHexCodec.decode_encoded]
  change (ShielddNativeParameterBytes.fixedBuffer bytes).bind
    (fun buffer => fq.parse (GroupByteCodec.reverseBytes buffer)) = none
  rw [ShielddNativeParameterBytes.fixedBuffer, dif_neg wrong]
  rfl

theorem asset_hash {F Q : Type} [Field F] [CharP F Scalar.modulus]
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F) (asset : Q) :
    (NativeAssetHashParameters.assetSource
      (ShielddNativeParameterBackend.hexCodec backend) fq arithmetic initial square asset).map
      (fun value => (fq.integer value : F)) =
      some (Poseidon.hash3 NativeAssetHashParameters.smallParameters 26 [(fq.integer asset : F)]) :=
  ShielddNativeParameterBackend.asset_hash_from_backend backend fq arithmetic initial square codec asset

set_option pp.all true in
#check @hex_backend
#print axioms hex_backend
set_option pp.all true in
#check @field_buffer
#print axioms field_buffer
set_option pp.all true in
#check @field_wrong_length
#print axioms field_wrong_length
set_option pp.all true in
#check @asset_hash
#print axioms asset_hash

end ShielddSecurity.ShielddHexParameterInstance
