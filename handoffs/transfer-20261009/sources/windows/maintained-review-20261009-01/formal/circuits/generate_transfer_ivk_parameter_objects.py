"""Exact native-object join over the accepted426-entry parameter instance.

Keeps the existing field-value module unchanged. Its finite certificates and
the canonical byte theorem derive object equality for both native loaders.
"""
from . import generate_transfer_ivk_parameter_readers as readers
from . import generate_transfer_ivk_reduction_join as joins


def generate(data, export, parameter_root, expected_relation, readonly_lcs=()):
    readers.generate(data, export, parameter_root, expected_relation, readonly_lcs)
    name = 'RuntimeTransferIvkParameterObjects'
    aliases = dict(R='RuntimeTransferIvkParameterReaders', C='ShielddNativeParameterCodec',
                   P='ShielddNativeParameterRead')
    source = '''import ShielddSecurity.RuntimeTransferIvkParameterReaders
import ShielddSecurity.ShielddNativeParameterCodec
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += '''private theorem entry_bounded (entry : Fin 426) : R.artifact entry < Scalar.modulus := by
  have checked : (List.finRange 426).all (fun entry => decide (R.artifact entry < Scalar.modulus)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp checked entry (List.mem_finRange entry))

theorem circuit_objects {F : Type} [Field F] [CharP F Scalar.modulus] {Raw Encoded : Type}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (codec : TransferReduction.CanonicalField F) :
    (fun entry : Fin 426 => ShielddNativeIvkHash.circuitConstant operations reader codec (R.signed entry : F)) =
      (fun entry => P.circuitParse operations reader (R.artifact entry)) := by
  funext entry
  have interpreted := congrArg (fun table : Fin 426 → F => table entry) (R.circuit_loaded operations reader)
  have cast : (R.artifact entry : F) = (R.signed entry : F) :=
    (P.circuit_parse_value operations reader (R.artifact entry) (entry_bounded entry)).symm.trans interpreted
  rw [← cast]
  exact C.circuit_load_cast operations reader codec (R.artifact entry) (entry_bounded entry)

theorem sdk_objects {F : Type} [Field F] [CharP F Scalar.modulus] {Q : Type}
    (fq : GroupNativeSdk.FqBytes Q) (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) :
    (fun entry : Fin 426 => ShielddNativeIvkHash.sdkConstant fq arithmetic codec (R.signed entry : F)) =
      (fun entry => P.sdkParse fq arithmetic (R.artifact entry)) := by
  funext entry
  have interpreted := congrArg (fun table : Fin 426 → F => table entry) (R.sdk_loaded fq arithmetic)
  have cast : (R.artifact entry : F) = (R.signed entry : F) :=
    (P.sdk_parse_value fq arithmetic (R.artifact entry) (entry_bounded entry)).symm.trans interpreted
  rw [← cast]
  exact C.sdk_load_cast fq arithmetic codec (R.artifact entry) (entry_bounded entry)
#print axioms circuit_objects
#print axioms sdk_objects
'''
    return name, joins._qualify(source + f'end ShielddSecurity.{name}\n', aliases)
