import ShielddSecurity.ShielddNativeIvkSdkProgram
import ShielddSecurity.ShielddViewingKeyAdmission

set_option maxHeartbeats 150000

namespace ShielddSecurity.ShielddViewingKeyScalar

variable {F : Type} [Field F] [CharP F Scalar.modulus] {Q R : Type}

/-- The scalar returned by the defined SDK admission guard is the Euclidean
reduction of its exact square-based hash program. Canonical Fq encoding and
the prime-field codec derive the integer interpretation; no desired scalar
value, hash result, private-column bound or row truth is assumed. -/
theorem scalar_integer (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F 6)
    (nk x y : Q) (scalar : R)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec parameters nk x y) = some scalar) :
    fr.integer scalar = codec.decode (Poseidon.hash6 parameters 16
      [ShielddNativeIvkHash.fqValue (F := F) fq nk,ShielddNativeIvkHash.fqValue (F := F) fq x,
       ShielddNativeIvkHash.fqValue (F := F) fq y]) % Scalar.order := by
  have chosen := (ShielddViewingKeyAdmission.successful_scalar primitives _ scalar accepted).1
  have meaning := ShielddNativeIvkSdkProgram.ivk_value fq arithmetic initial square codec parameters nk x y
  have decoded : codec.decode (Poseidon.hash6 parameters 16
      [ShielddNativeIvkHash.fqValue (F := F) fq nk,ShielddNativeIvkHash.fqValue (F := F) fq x,
       ShielddNativeIvkHash.fqValue (F := F) fq y]) =
      fq.integer (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec parameters nk x y) := by
    rw [← meaning]
    exact TransferReduction.decode_canonical_cast codec _ (fq.bounded _)
  rw [chosen,ShielddViewingKeyAdmission.reduce_integer,decoded]

theorem scalar_value (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F 6)
    (nk x y : Q) (scalar : R)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec parameters nk x y) = some scalar) :
    (fr.integer scalar : F) =
      ((codec.decode (Poseidon.hash6 parameters 16
        [ShielddNativeIvkHash.fqValue (F := F) fq nk,ShielddNativeIvkHash.fqValue (F := F) fq x,
         ShielddNativeIvkHash.fqValue (F := F) fq y]) % Scalar.order : Nat) : F) :=
  congrArg (fun value : Nat => (value : F))
    (scalar_integer fq fr arithmetic initial square primitives codec parameters nk x y scalar accepted)

set_option pp.all true in
#check @scalar_integer
#print axioms scalar_integer
set_option pp.all true in
#check @scalar_value
#print axioms scalar_value

end ShielddSecurity.ShielddViewingKeyScalar
