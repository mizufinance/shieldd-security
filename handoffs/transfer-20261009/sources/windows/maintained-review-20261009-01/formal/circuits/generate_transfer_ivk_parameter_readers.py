"""Finite actual ARK/MDS entry join for the two globally defined readers.

The existing typed selector reaccepts the source cone and exact parameter
artifact. This renderer never scans ordinary rows or qualifies Rust source.
"""
from . import generate_transfer_prefix_hash_completion as hashes
from . import generate_transfer_ivk_reduction_join as joins


def generate(data, export, parameter_root, expected_relation, readonly_lcs=()):
    selected, _, _ = hashes.select_ivk(data, export, parameter_root, expected_relation, readonly_lcs)
    call = selected['calls'][0]
    parameters = call['parameters']
    hashes.actual_ivk_call(selected)
    coefficients = [value for row in parameters['ark'] for value in row]
    coefficients.extend(value for row in parameters['mds'] for value in row)
    if (len(parameters['ark']) != 65 or len(parameters['mds']) != 6
            or any(len(row) != 6 for row in parameters['ark'] + parameters['mds'])
            or len(coefficients) != 426
            or any(type(value) is not int or not 0 <= value < hashes.relation.MODULUS
                   for value in coefficients)):
        raise hashes.relation.RelationError('native IVK exact426 canonical artifact entries')
    name = 'RuntimeTransferIvkParameterReaders'
    aliases = dict(D='RuntimeHashBlock_authorization_ivk_0', P='ShielddNativeParameterRead')
    source = '''import ShielddSecurity.RuntimeIvkHash_Data
import ShielddSecurity.ShielddNativeParameterRead
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += 'def artifactValues : List Nat := [' + ','.join(map(str, coefficients)) + ']\n'
    source += '''def artifact (entry : Fin 426) : Nat := artifactValues[entry.val]?.getD 0
def signed (entry : Fin 426) : Int :=
  if entry.val < 390 then D.parameters.ark (entry.val/6) ⟨entry.val%6,Nat.mod_lt _ (by decide)⟩
  else D.parameters.mds ⟨(entry.val-390)/6,by have := entry.isLt; omega⟩
    ⟨(entry.val-390)%6,Nat.mod_lt _ (by decide)⟩
private theorem entry_checked (entry : Fin 426) :
    artifact entry < Scalar.modulus ∧ (artifact entry : Int) = signed entry % (Scalar.modulus : Int) := by
  have checked : (List.finRange 426).all (fun entry => decide
    (artifact entry < Scalar.modulus ∧ (artifact entry : Int) = signed entry % (Scalar.modulus : Int))) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp checked entry (List.mem_finRange entry))
private theorem entry_cast {F : Type} [Field F] [CharP F Scalar.modulus] (entry : Fin 426) :
    (artifact entry : F) = (signed entry : F) := by
  have lifted := congrArg (fun value : Int => (value : F)) (entry_checked entry).2
  simpa only [Int.cast_natCast] using lifted.trans (Compiler.coefficient_mod (F := F) (p := Scalar.modulus) (signed entry))
theorem circuit_loaded {F : Type} [Field F] [CharP F Scalar.modulus] {Raw Encoded : Type}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) :
    (fun entry : Fin 426 => ShielddNativeScalar.value operations
      (P.circuitParse operations reader (artifact entry))) = (fun entry => (signed entry : F)) := by
  funext entry
  exact (P.circuit_parse_value operations reader (artifact entry) (entry_checked entry).1).trans (entry_cast entry)
theorem sdk_loaded {F : Type} [Field F] [CharP F Scalar.modulus] {Q : Type}
    (fq : GroupNativeSdk.FqBytes Q) (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq) :
    (fun entry : Fin 426 => ShielddNativeIvkHash.fqValue (F := F) fq
      (P.sdkParse fq arithmetic (artifact entry))) = (fun entry => (signed entry : F)) := by
  funext entry
  exact (P.sdk_parse_value fq arithmetic (artifact entry) (entry_checked entry).1).trans (entry_cast entry)
#print axioms circuit_loaded
#print axioms sdk_loaded
'''
    return name, joins._qualify(source + f'end ShielddSecurity.{name}\n', aliases)
