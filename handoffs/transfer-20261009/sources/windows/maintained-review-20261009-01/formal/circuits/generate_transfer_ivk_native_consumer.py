"""Derive the actual constructed IVK consumer from the returned SDK scalar.

Reuses accepted typed plans and owned hash/reduction/inverse constructors.
No ordinary scan, desired scalar value, or prior-row satisfaction is supplied.
Generated candidates require independent kernel/signature/assumption audits.
"""
from . import generate_transfer_ivk_key_prefix as keys
from . import generate_transfer_ivk_reduction_join as joins


def generate(ivk_data, ivk_export, reduction_data, reduction_export,
             parameter_root, expected_relation, readonly_lcs=()):
    keys.generate(ivk_data, ivk_export, reduction_data, reduction_export,
                  parameter_root, expected_relation, readonly_lcs)
    accepted = keys.native.hashes.ivk.inspect_metadata(
        ivk_data, parameter_root, expected_relation)
    plan = keys.native.reduction.plan(reduction_data, accepted, reduction_export,
                                     expected_relation, readonly_lcs)
    q, r = plan['phases'][:2]
    qcol, rcol = q['value'][0][0], r['value'][0][0]
    qs, rs = q['start'], r['start']
    copy = plan['checked']['metadata']['constant_copy']
    name = 'RuntimeTransferIvkNativeConsumerOwned'
    aliases = dict(P='RuntimeTransferIvkInversePrefixJoin',
        N='RuntimeTransferIvkNativeInverseOwned', S='ShielddViewingKeySeed',
        V='ShielddViewingKeyScalar', C='RuntimeTransferIvkHashReductionJoin',
        H='RuntimeTransferIvkHashOwnedCompletion', O=joins.ORDER,
        I='RuntimeTransferIvkInverseOwnedCompletion',
        D='RuntimeHashBlock_authorization_ivk_0')
    source = '''import ShielddSecurity.RuntimeTransferIvkKeyPrefixOwned
import ShielddSecurity.ShielddViewingKeyScalar
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += f'''private theorem actual_inputs : D.callInputs = S.hashInputs := by decide
private theorem hash_kept : ∀ term ∈ O.hashValue, term.1 ∈ O.kept ∧ term.1 ∉ [{qcol},{rcol}] ∧
    (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧ (term.1 < {rs} ∨ {rs+252} ≤ term.1) := by
  have checked : O.hashValue.all (fun term => decide (term.1 ∈ O.kept ∧ term.1 ∉ [{qcol},{rcol}] ∧
    (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧ (term.1 < {rs} ∨ {rs+252} ≤ term.1))) = true := by decide
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)
private theorem seed_hash {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F)
    (base : Nat → F) :
    eval (C.completed codec base) O.hashValue = eval (H.completeAssignment base) O.hashValue :=
  ScalarReductionSupport.hash_preserved (H.completeAssignment base) codec
    (eval (H.completeAssignment base) O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered O.hashValue hash_kept
private theorem inverse_keeps_consumer {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    eval (P.completed codec base) I.denominator = eval (C.completed codec base) I.denominator := by
  apply eval_agrees
  intro term member
  exact I.preserves _ term.1 (I.fresh term
    (List.mem_append_left I.remainder (List.mem_append_right I.numerator member)))
theorem constructed_consumer {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    eval (P.completed codec base) I.denominator =
      ((codec.decode (Poseidon.hash6 (Poseidon.castParameters D.parameters) 16
        (D.callInputs.map (eval base))) % Scalar.order : Nat) : F) := by
  have same := (seed_hash codec base).symm.trans (C.hash_value codec base one linked)
  rw [inverse_keeps_consumer,P.consumer_value,ScalarReductionSeed.remainder,same]

variable {{F : Type}} [Field F] {{Q R Encoded Native : Type}}
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q) (scalar : R) (base : Nat → F)
variable (one : base 0 = 1) (linked : base {copy} = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
    (Poseidon.castParameters D.parameters) nk x y) = some scalar)

include arithmetic initial square primitives one linked accepted in
theorem native_consumer_value [CharP F Scalar.modulus] :
    eval (N.completeAssignment fq backend codec nk x y base) I.denominator = (fr.integer scalar : F) := by
  have seedOne : S.seed fq backend nk x y base 0 = 1 :=
    (S.seed_preserves fq backend nk x y base 0 (by decide)).trans one
  have seedLink : S.seed fq backend nk x y base {copy} = S.seed fq backend nk x y base 0 := by
    rw [S.seed_preserves fq backend nk x y base {copy} (by decide),
      S.seed_preserves fq backend nk x y base 0 (by decide),linked]
  have consumer := constructed_consumer codec (S.seed fq backend nk x y base) seedOne seedLink
  rw [actual_inputs,S.seed_inputs] at consumer
  exact consumer.trans (V.scalar_value fq fr arithmetic initial square primitives codec
    (Poseidon.castParameters D.parameters) nk x y scalar accepted).symm

include arithmetic initial square primitives one linked accepted in
theorem native_consumer_integer [CharP F Scalar.modulus] :
    codec.decode (eval (N.completeAssignment fq backend codec nk x y base) I.denominator) =
      fr.integer scalar := by
  rw [native_consumer_value fq fr arithmetic initial square primitives backend codec nk x y scalar base one linked accepted]
  exact TransferReduction.decode_canonical_cast codec _
    (lt_trans (fr.bounded scalar) (by decide : Scalar.order < Scalar.modulus))

include arithmetic initial square primitives one linked accepted in
theorem native_reader_consumer [CharP F Scalar.modulus] :
    GroupNativeSdk.readScalar fq fr (ShielddScalarReader.decoder backend) scalar =
      some (eval (N.completeAssignment fq backend codec nk x y base) I.denominator) := by
  rw [native_consumer_value fq fr arithmetic initial square primitives backend codec nk x y scalar base one linked accepted]
  exact GroupNativeSdk.scalar_read fq fr (ShielddScalarReader.decoder backend) scalar
'''
    for export in ('constructed_consumer', 'native_consumer_value',
                   'native_consumer_integer', 'native_reader_consumer'):
        source += '#print axioms ' + export + '\n'
    return name, joins._qualify(source+f'end ShielddSecurity.{name}\n', aliases)
