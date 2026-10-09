"""Complete actual IVK rows from the owned square-based SDK admission.

Reuse the accepted actual hash/reduction/inverse plan. Nonzero inverse legality
follows from the actual successful Fr guard and the proved native hash integer
law, without assuming a circuit denominator or a second accepted hash object.
"""
from . import generate_transfer_ivk_native_bit_values as values
from . import generate_transfer_ivk_reduction_join as joins


def generate(ivk_data,ivk_export,reduction_data,reduction_export,
             parameter_root,expected_relation,readonly_lcs=()):
    values.generate(ivk_data,ivk_export,reduction_data,reduction_export,
                    parameter_root,expected_relation,readonly_lcs)
    native=values.bits.consumer.keys.native
    accepted=native.hashes.ivk.inspect_metadata(ivk_data,parameter_root,expected_relation)
    plan=native.reduction.plan(reduction_data,accepted,reduction_export,expected_relation,readonly_lcs)
    copy=plan['checked']['metadata']['constant_copy']
    name='RuntimeTransferIvkNativeProgramRows'
    aliases=dict(P='RuntimeTransferIvkInversePrefixJoin',S='ShielddViewingKeySeed',
        N='RuntimeTransferIvkNativeInverseOwned',D='RuntimeHashBlock_authorization_ivk_0')
    source='''import ShielddSecurity.RuntimeTransferIvkNativeConsumerOwned
set_option maxHeartbeats 250000
set_option maxRecDepth 4096
'''+f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {value}\n' for key,value in aliases.items())
    source+=f'''private theorem actual_inputs : D.callInputs = S.hashInputs := by decide
theorem original_rows_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    {{Q R Encoded Native : Type}} (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (codec : TransferReduction.CanonicalField F) (nk x y : Q) (scalar : R) (base : Nat → F)
    (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
        (Poseidon.castParameters D.parameters) nk x y) = some scalar) :
    Satisfies (N.completeAssignment fq backend codec nk x y base) P.originalRows := by
  have scalarMeaning := ShielddViewingKeyScalar.scalar_integer fq fr arithmetic initial square primitives codec
    (Poseidon.castParameters D.parameters) nk x y scalar accepted
  have positive := (ShielddViewingKeyAdmission.successful_scalar primitives _ scalar accepted).2.1
  have nonzero : codec.decode (Poseidon.hash6 (Poseidon.castParameters D.parameters) 16
      [ShielddNativeIvkHash.fqValue (F := F) fq nk,ShielddNativeIvkHash.fqValue (F := F) fq x,
       ShielddNativeIvkHash.fqValue (F := F) fq y]) % Scalar.order ≠ 0 := by
    rw [← scalarMeaning]
    exact Nat.ne_of_gt positive
  have seededOne : S.seed fq backend nk x y base 0 = 1 :=
    (S.seed_preserves fq backend nk x y base 0 (by decide)).trans one
  have seededLink : S.seed fq backend nk x y base {copy} = S.seed fq backend nk x y base 0 := by
    rw [S.seed_preserves fq backend nk x y base {copy} (by decide),
      S.seed_preserves fq backend nk x y base 0 (by decide),linked]
  apply P.original_complete codec (S.seed fq backend nk x y base) seededOne four seededLink
  rw [actual_inputs,S.seed_inputs]
  exact nonzero
#print axioms original_rows_complete
'''
    return name,joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)
