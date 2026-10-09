import ShielddSecurity.NativeEphemeralAdmission
import ShielddSecurity.GroupNativeGenerator

set_option maxHeartbeats 150000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEphemeralGenerator

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]

theorem valid_decoded_scalar (codec : TransferReduction.CanonicalField F) (value : F)
    (valid : NativeEphemeralAdmission.validScalar codec value) :
    0 < codec.decode value ∧ codec.decode value < Scalar.order := by
  have nonzero : codec.decode value ≠ 0 := by
    intro zero
    apply valid.1
    have same := codec.roundtrip value
    rw [zero,Nat.cast_zero] at same
    exact same.symm
  exact ⟨Nat.pos_of_ne_zero nonzero,valid.2⟩

/-- The owned native point multiplication and byte reader, plus the global
exact standard-generator order, derive the inverse used by EPK row construction.
The published point/source LC and fixed-window transport are separate joins. -/
theorem native_ephemeral_inverse {J : Type} [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (two : (2 : F) ≠ 0) (generator : J) (exactOrder : addOrderOf generator = Scalar.order)
    (value : F) (valid : NativeEphemeralAdmission.validScalar codec value) :
    (NativeTransferAdmission.nativeMultiply codec writer d (model.coordinates generator) value).x *
      ((NativeTransferAdmission.nativeMultiply codec writer d (model.coordinates generator) value).x)⁻¹ = 1 := by
  have decoded := valid_decoded_scalar codec value valid
  unfold NativeTransferAdmission.nativeMultiply
  rw [GroupByteCodec.native_reader_coordinates codec writer d imaginary model nonSquare imaginarySquare two]
  exact GroupNativeGenerator.canonical_multiple_inverse d model generator exactOrder
    (codec.decode value) decoded.1 decoded.2

/-- Pinned encryption.rs checks all four ephemeral scalars before building
sender/output core/ext EPKs with group::generator().multiply. Success propagates
both audit ownership guards. No statement or verifier Boolean is used here. -/
theorem encryption_ephemeral_inverse {J Ownership Payload : Type} [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (two : (2 : F) ≠ 0) (generator : J) (exactOrder : addOrderOf generator = Scalar.order)
    (ephemeral : Fin 4 → F) (ownership : Fin 2 → F) (checking : Group.Point F)
    (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) (value : Payload)
    (accepted : NativeEphemeralAdmission.encryptionNative codec ephemeral ownership checking ownershipBuild build = .ok value)
    (index : Fin 4) :
    (NativeTransferAdmission.nativeMultiply codec writer d (model.coordinates generator) (ephemeral index)).x *
      ((NativeTransferAdmission.nativeMultiply codec writer d (model.coordinates generator) (ephemeral index)).x)⁻¹ = 1 := by
  have guards := NativeEphemeralAdmission.encryption_success codec ephemeral ownership checking
    ownershipBuild build value accepted
  exact native_ephemeral_inverse codec writer d imaginary model nonSquare imaginarySquare two
    generator exactOrder (ephemeral index) (guards.1 index)

set_option pp.all true in
#check @valid_decoded_scalar
#print axioms valid_decoded_scalar
set_option pp.all true in
#check @native_ephemeral_inverse
#print axioms native_ephemeral_inverse
set_option pp.all true in
#check @encryption_ephemeral_inverse
#print axioms encryption_ephemeral_inverse

end ShielddSecurity.NativeEphemeralGenerator
