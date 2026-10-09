"""Pointwise field meanings of the actual IVK columns from owned writeBits.

The exact SDK returned Fr integer is joined through the proved native bit-list
consumer. There is no Boolean-row or desired scalar/coordinate premise.
"""
from . import generate_transfer_ivk_native_bits as bits
from . import generate_transfer_ivk_reduction_join as joins


def generate(ivk_data, ivk_export, reduction_data, reduction_export,
             parameter_root, expected_relation, readonly_lcs=()):
    bits.generate(ivk_data,ivk_export,reduction_data,reduction_export,
                  parameter_root,expected_relation,readonly_lcs)
    native=bits.consumer.keys.native
    accepted=native.hashes.ivk.inspect_metadata(ivk_data,parameter_root,expected_relation)
    plan=native.reduction.plan(reduction_data,accepted,reduction_export,expected_relation,readonly_lcs)
    q,r=plan['phases'][:2];qcol,rcol=q['value'][0][0],r['value'][0][0]
    qs,rs=q['start'],r['start'];copy=plan['checked']['metadata']['constant_copy']
    if r['width']!=252 or r['columns']!=list(range(rs,rs+252)):
        raise native.reduction.relation.RelationError('actual IVK field-bit source order/width')
    name='RuntimeTransferIvkNativeBitValuesOwned'
    aliases=dict(B='RuntimeTransferIvkNativeBitsOwned',P='RuntimeTransferIvkInversePrefixJoin',
        I='RuntimeTransferIvkInverseOwnedCompletion',N='RuntimeTransferIvkNativeInverseOwned',
        H='RuntimeTransferIvkHashOwnedCompletion',O=joins.ORDER,S='ShielddViewingKeySeed',
        D='RuntimeHashBlock_authorization_ivk_0')
    source='''import ShielddSecurity.RuntimeTransferIvkNativeBitsOwned
import ShielddSecurity.ScalarWrittenBitValues
set_option maxHeartbeats 250000
set_option maxRecDepth 4096
'''+f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {value}\n' for key,value in aliases.items())
    source+=f'''private theorem bit_frame : ∀ column ∈ List.range' {rs} 252, column ∉ I.ownedWrites := by
  have checked : (List.range' {rs} 252).all (fun column => decide (column ∉ I.ownedWrites)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
theorem constructed_values {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (index : Nat) (bound : index < 252) :
    P.completed codec base ({rs}+index) =
      (if (encodeBits 252 (ScalarReductionSeed.remainder codec
        (eval (H.completeAssignment base) O.hashValue)))[index]?.getD false then 1 else 0) := by
  let hbase := H.completeAssignment base
  let value := eval hbase O.hashValue
  let writtenBase := writeBits (ScalarReductionSeed.seed hbase codec value {qcol} {rcol})
    {qs} (encodeBits 4 (ScalarReductionSeed.quotient codec value))
  have kept : ∀ column ∈ List.range' {rs}
      (encodeBits 252 (ScalarReductionSeed.remainder codec value)).length,
      P.completed codec base column =
        writeBits writtenBase {rs} (encodeBits 252 (ScalarReductionSeed.remainder codec value)) column := by
    intro column member
    have actual : column ∈ List.range' {rs} 252 := by
      simpa only [encodeBits_length] using member
    exact (I.preserves _ column (bit_frame column actual)).trans
      (ScalarReductionSupport.written_remainder_bits hbase codec value {qcol} {rcol} {qs} {rs}
        O.allStages O.kept O.ordered column actual)
  exact ScalarWrittenBitValues.preserved_bit_value writtenBase (P.completed codec base) {rs}
    (encodeBits 252 (ScalarReductionSeed.remainder codec value)) kept index
    (by simpa only [encodeBits_length] using bound)

theorem native_values {{F : Type}} [Field F] [CharP F Scalar.modulus] {{Q R Encoded Native : Type}}
    (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (codec : TransferReduction.CanonicalField F) (nk x y : Q) (scalar : R) (base : Nat → F)
    (one : base 0 = 1) (linked : base {copy} = base 0)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
        (Poseidon.castParameters D.parameters) nk x y) = some scalar)
    (index : Nat) (bound : index < 252) :
    N.completeAssignment fq backend codec nk x y base ({rs}+index) =
      (if (encodeBits 252 (fr.integer scalar))[index]?.getD false then 1 else 0) := by
  let seeded := S.seed fq backend nk x y base
  have same : encodeBits 252 (ScalarReductionSeed.remainder codec
      (eval (H.completeAssignment seeded) O.hashValue)) = encodeBits 252 (fr.integer scalar) :=
    (B.constructed_bits codec seeded).symm.trans
      (B.native_bits fq fr arithmetic initial square primitives backend codec nk x y scalar base one linked accepted)
  have values := constructed_values codec seeded index bound
  rw [same] at values
  exact values
'''
    for export in ('constructed_values','native_values'):
        source+='#print axioms '+export+'\n'
    return name,joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)
