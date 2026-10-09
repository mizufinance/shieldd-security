"""Bind actual written IVK bits to the SDK's returned canonical Fr integer.

Bit meanings come from writeBits and preserved columns, independently of
modular reconstruction injection. Input acceptance and row plans are reused.
"""
from . import generate_transfer_ivk_native_consumer as consumer
from . import generate_transfer_ivk_reduction_join as joins


def generate(ivk_data, ivk_export, reduction_data, reduction_export,
             parameter_root, expected_relation, readonly_lcs=()):
    consumer.generate(ivk_data, ivk_export, reduction_data, reduction_export,
                       parameter_root, expected_relation, readonly_lcs)
    native = consumer.keys.native
    accepted = native.hashes.ivk.inspect_metadata(ivk_data, parameter_root, expected_relation)
    plan = native.reduction.plan(reduction_data, accepted, reduction_export,
                                 expected_relation, readonly_lcs)
    q, r = plan['phases'][:2]
    qcol, rcol = q['value'][0][0], r['value'][0][0]
    qs, rs = q['start'], r['start']
    if r['width'] != 252 or r['columns'] != list(range(rs, rs+252)):
        raise native.reduction.relation.RelationError('actual IVK source bit order/width')
    name = 'RuntimeTransferIvkNativeBitsOwned'
    aliases = dict(P='RuntimeTransferIvkInversePrefixJoin',
        N='RuntimeTransferIvkNativeInverseOwned', S='ShielddViewingKeySeed',
        V='RuntimeTransferIvkNativeConsumerOwned', C='RuntimeTransferIvkHashReductionJoin',
        H='RuntimeTransferIvkHashOwnedCompletion', O=joins.ORDER,
        I='RuntimeTransferIvkInverseOwnedCompletion', D='RuntimeHashBlock_authorization_ivk_0')
    source = '''import ShielddSecurity.RuntimeTransferIvkNativeConsumerOwned
import ShielddSecurity.ScalarConstructedBits
import ShielddSecurity.GroupByteCodec
set_option maxHeartbeats 250000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += f'''def bitColumns : List Nat := List.range' {rs} 252
def sourceBits : List Linear := bitColumns.map (fun column => [(column,1)])
private theorem bit_frame : ∀ column ∈ bitColumns, column ∉ I.ownedWrites := by
  have checked : bitColumns.all (fun column => decide (column ∉ I.ownedWrites)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
private theorem inverse_keeps_consumer {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    eval (P.completed codec base) I.denominator = eval (C.completed codec base) I.denominator := by
  apply eval_agrees
  intro term member
  exact I.preserves _ term.1 (I.fresh term
    (List.mem_append_left I.remainder (List.mem_append_right I.numerator member)))
theorem constructed_bits {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    ScalarBits.decodeBits (P.completed codec base) sourceBits =
      encodeBits 252 (ScalarReductionSeed.remainder codec (eval (H.completeAssignment base) O.hashValue)) := by
  let hbase := H.completeAssignment base
  let value := eval hbase O.hashValue
  let written := writeBits (writeBits (ScalarReductionSeed.seed hbase codec value {qcol} {rcol})
    {qs} (encodeBits 4 (ScalarReductionSeed.quotient codec value)))
    {rs} (encodeBits 252 (ScalarReductionSeed.remainder codec value))
  have kept : ∀ column ∈ bitColumns, P.completed codec base column = written column := by
    intro column member
    exact (I.preserves _ column (bit_frame column member)).trans
      (ScalarReductionSupport.written_remainder_bits hbase codec value {qcol} {rcol} {qs} {rs}
        O.allStages O.kept O.ordered column member)
  have mapped : bitColumns.map (P.completed codec base) = bitColumns.map written :=
    List.map_congr_left kept
  apply ScalarConstructedBits.decoded_singletons
  have writtenValues := writeBits_map
    (writeBits (ScalarReductionSeed.seed hbase codec value {qcol} {rcol})
      {qs} (encodeBits 4 (ScalarReductionSeed.quotient codec value)))
      {rs} (encodeBits 252 (ScalarReductionSeed.remainder codec value))
  exact mapped.trans (by simpa only [bitColumns,written,encodeBits_length] using writtenValues)

theorem native_bits {{F : Type}} [Field F] [CharP F Scalar.modulus] {{Q R Encoded Native : Type}}
    (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (codec : TransferReduction.CanonicalField F) (nk x y : Q) (scalar : R) (base : Nat → F)
    (one : base 0 = 1) (linked : base {plan['checked']['metadata']['constant_copy']} = base 0)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
        (Poseidon.castParameters D.parameters) nk x y) = some scalar) :
    ScalarBits.decodeBits (N.completeAssignment fq backend codec nk x y base) sourceBits =
      encodeBits 252 (fr.integer scalar) := by
  let seeded := S.seed fq backend nk x y base
  have chosen := V.native_consumer_integer fq fr arithmetic initial square primitives
    backend codec nk x y scalar base one linked accepted
  change codec.decode (eval (P.completed codec seeded) I.denominator) = fr.integer scalar at chosen
  rw [inverse_keeps_consumer,P.consumer_value] at chosen
  have bound : ScalarReductionSeed.remainder codec (eval (H.completeAssignment seeded) O.hashValue) <
      Scalar.modulus := lt_trans
    (ScalarReductionCompletion.decoded_operands codec (eval (H.completeAssignment seeded) O.hashValue)).2.1
    (by decide : Scalar.order < Scalar.modulus)
  rw [TransferReduction.decode_canonical_cast codec _ bound] at chosen
  have bits := constructed_bits codec seeded
  rw [chosen] at bits
  exact bits

theorem native_reader_bits {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (base : Nat → F) :
    GroupByteCodec.reader (writer.encode (eval (P.completed codec base) I.denominator)) =
      ScalarBits.decodeBits (P.completed codec base) sourceBits ++ [false,false,false] := by
  let value := ScalarReductionSeed.remainder codec (eval (H.completeAssignment base) O.hashValue)
  have bound : value < Scalar.order :=
    (ScalarReductionCompletion.decoded_operands codec (eval (H.completeAssignment base) O.hashValue)).2.1
  have small : value < 2^252 := lt_trans bound GroupScalarCodec.scalar_order_width
  have decoded := constructed_bits codec base
  have width : (ScalarBits.decodeBits (P.completed codec base) sourceBits).length = 252 := by
    rw [decoded,encodeBits_length]
  have integer : binary (ScalarBits.decodeBits (P.completed codec base) sourceBits) = value := by
    rw [decoded]
    exact encodeBits_value 252 value small
  apply GroupByteCodec.canonical_reader_join codec writer _ width _
  · rw [integer]
    exact bound
  · rw [integer,inverse_keeps_consumer,P.consumer_value]
'''
    for export in ('constructed_bits', 'native_bits', 'native_reader_bits'):
        source += '#print axioms ' + export + '\n'
    return name, joins._qualify(source+f'end ShielddSecurity.{name}\n', aliases)
