import ShielddSecurity.RuntimeTransferStatementPublicHash
import ShielddSecurity.TransferEncryptionSdkShielddNativeFieldHashLoaded

set_option maxHeartbeats 600000

namespace ShielddSecurity.TransferStatementNativeHash

/-- The two independently captured owned wide recipes are the same table.
This is a kernel equality of their complete parameters, not a hash comparison. -/
theorem parameters_equal :
    RuntimeTransferEncryptionHashGroup0.wideRecipe =
      RuntimeHashBlock_remaining0_statement97_permutation0_0.parameters := by
  rfl

theorem inputs_length : RuntimeTransferStatementHashDomain34Layout.inputs.length = 64 := by
  rfl

variable {F Q Encoded : Type} [Field F] [CharP F Scalar.modulus]
variable (hex : TransferEncryptionSdkShielddNativeParameterBytes.HexCodec Encoded)
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : TransferEncryptionSdkShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : TransferEncryptionSdkShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)

/-- Canonical native images of the actual sixty-four captured row expressions.
Association with the owned caller's decoded statement fields is a separate join. -/
def nativeInputs (rho : Nat → F) : List Q :=
  RuntimeTransferStatementHashDomain34Layout.inputs.map (fun input =>
    ShielddNativeIvkHash.sdkConstant fq arithmetic codec (eval rho input))

def nativeCall (rho : Nat → F) : Option Q :=
  TransferEncryptionSdkShielddNativeFieldHashLoaded.loadedHash hex fq arithmetic initial square
    34 (nativeInputs fq arithmetic codec rho)

theorem inputs_value (rho : Nat → F) :
    (nativeInputs fq arithmetic codec rho).map (ShielddNativeIvkHash.fqValue (F := F) fq) =
      RuntimeTransferStatementHashDomain34Layout.inputs.map (eval rho) := by
  simp only [nativeInputs, List.map_map, Function.comp_def, ShielddNativeIvkHash.sdk_constant_value]

/-- Public input column one equals the owned loaded callback on these actual
row-expression images, under its global primitive contracts and actual rows.
Neither a successful callback nor a desired public hash is a premise. -/
theorem public_value (rho : Nat → F) (one : rho 0 = 1)
    (publicRows : Satisfies rho RuntimeTransferStatementPublicHash.rawRows)
    (hashRows : Satisfies rho RuntimeTransferStatementHashDomain34Layout.rawRows) :
    (nativeCall hex fq arithmetic initial square codec rho).map
      (ShielddNativeIvkHash.fqValue (F := F) fq) = some (rho 1) := by
  have length : (nativeInputs fq arithmetic codec rho).length = 64 := by
    simp only [nativeInputs, List.length_map, inputs_length]
  have bounded : (nativeInputs fq arithmetic codec rho).length * 256 + 34 < 2^64 := by
    rw [length]
    decide
  have native := TransferEncryptionSdkShielddNativeFieldHashLoaded.hash_value
    hex fq arithmetic initial square codec 34 (nativeInputs fq arithmetic codec rho) bounded
  rw [inputs_value fq arithmetic codec rho] at native
  have fieldLength : (RuntimeTransferStatementHashDomain34Layout.inputs.map (eval rho)).length = 64 := by
    simp only [List.length_map, inputs_length]
  have publicEquality := RuntimeTransferStatementPublicHash.actual_public_hash rho one publicRows hashRows
  simpa only [nativeCall, Poseidon.hash, if_neg (by omega :
      ¬ (RuntimeTransferStatementHashDomain34Layout.inputs.map (eval rho)).length ≤ 2),
    TransferEncryptionSdkShielddNativeFieldHashLoaded.wideParameters, parameters_equal, publicEquality] using native

theorem public_integer (rho : Nat → F) (one : rho 0 = 1)
    (publicRows : Satisfies rho RuntimeTransferStatementPublicHash.rawRows)
    (hashRows : Satisfies rho RuntimeTransferStatementHashDomain34Layout.rawRows) :
    (nativeCall hex fq arithmetic initial square codec rho).map fq.integer =
      some (codec.decode (rho 1)) := by
  have value := public_value hex fq arithmetic initial square codec rho one publicRows hashRows
  cases result : nativeCall hex fq arithmetic initial square codec rho with
  | none => simp only [result, Option.map_none, reduceCtorEq] at value
  | some native =>
    have fieldValue : ShielddNativeIvkHash.fqValue (F := F) fq native = rho 1 := by
      simpa only [result, Option.map_some, Option.some.injEq] using value
    have integerValue : fq.integer native = codec.decode (rho 1) := by
      rw [← fieldValue]
      exact (TransferReduction.decode_canonical_cast codec (fq.integer native) (fq.bounded native)).symm
    simpa only [result, Option.map_some] using congrArg some integerValue

set_option pp.all true in
#check @parameters_equal
#print axioms parameters_equal
set_option pp.all true in
#check @inputs_length
#print axioms inputs_length
set_option pp.all true in
#check @inputs_value
#print axioms inputs_value
set_option pp.all true in
#check @public_value
#print axioms public_value
set_option pp.all true in
#check @public_integer
#print axioms public_integer

end ShielddSecurity.TransferStatementNativeHash
