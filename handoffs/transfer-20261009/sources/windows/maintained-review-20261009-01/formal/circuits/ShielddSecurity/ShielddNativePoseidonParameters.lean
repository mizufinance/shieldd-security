import ShielddSecurity.ShielddNativeIvkHash

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativePoseidonParameters
open GroupByteCodec

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- The circuit renderer uses either the canonical integer or that integer
minus the field modulus. This data relation contains no hash result. -/
def Represents (signed : Int) (canonical : Nat) : Prop :=
  signed = (canonical : Int) ∨ signed = (canonical : Int) - (Scalar.modulus : Int)

theorem coefficient_cast (signed : Int) (canonical : Nat)
    (represented : Represents signed canonical) : (signed : F) = (canonical : F) := by
  rcases represented with same | shifted
  · simp only [same,Int.cast_natCast]
  · rw [shifted]
    exact signed_coefficient (F := F) (p := Scalar.modulus) canonical

theorem coefficient_decoder (codec : TransferReduction.CanonicalField F)
    (signed : Int) (canonical : Nat) (bounded : canonical < Scalar.modulus)
    (represented : Represents signed canonical) : codec.decode (signed : F) = canonical := by
  rw [coefficient_cast signed canonical represented]
  exact TransferReduction.decode_canonical_cast codec canonical bounded

def sourceBuffer (canonical : Nat) : Bytes :=
  fun index => ⟨littleEndianByte canonical index.val,Nat.mod_lt _ (by decide)⟩

/-- The SDK reverses its canonical BE coefficient into this LE buffer. The
global hex/JSON functional parser and its exact source instantiation remain
separate from the field codec contract. -/
theorem coefficient_bytes (codec : TransferReduction.CanonicalField F)
    (signed : Int) (canonical : Nat) (bounded : canonical < Scalar.modulus)
    (represented : Represents signed canonical) :
    ShielddNativeIvkHash.littleEndianWrite codec (signed : F) = sourceBuffer canonical := by
  funext index
  apply Fin.ext
  change littleEndianByte (codec.decode (signed : F)) index.val =
    littleEndianByte canonical index.val
  rw [coefficient_decoder codec signed canonical bounded represented]

theorem parsed_coefficient {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F)
    (signed : Int) (canonical : Nat) (bounded : canonical < Scalar.modulus)
    (represented : Represents signed canonical) :
    ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed : F) =
      (fq.parse (sourceBuffer canonical)).getD arithmetic.zero := by
  unfold ShielddNativeIvkHash.sdkConstant
  rw [coefficient_bytes codec signed canonical bounded represented]

set_option pp.all true in
#check @coefficient_cast
#print axioms coefficient_cast
set_option pp.all true in
#check @coefficient_decoder
#print axioms coefficient_decoder
set_option pp.all true in
#check @coefficient_bytes
#print axioms coefficient_bytes
set_option pp.all true in
#check @parsed_coefficient
#print axioms parsed_coefficient
end ShielddSecurity.ShielddNativePoseidonParameters
