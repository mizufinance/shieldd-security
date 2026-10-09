"""Compose actual cipher assertions with canonical native hash images.

The result describes values and canonical integers of the owned arithmetic
program. Caller objects, group input bindings and the full Transfer stay open.
"""
import re

NAME = 'TransferEncryptionNativeCipherGraph'
FIELD = 'RuntimeTransferEncryptionFieldCipherGraph'
HASH = 'TransferEncryptionNativeHashGraph'
GRAPH = 'RuntimeTransferEncryptionHashGraph'


def generate(cases, seeds):
    assert cases == [('detection0',6,'[(6,1)]'),
                     ('detection1',7,f'{GRAPH}.output 0'),
                     ('detection2',8,'[(108486,1)]'),('detection3',9,'[]'),
                     ('core0_confirmation',11,None),('core0_amount',12,'[(4789,1)]'),
                     ('core2_confirmation',14,None),('core2_amount',15,'[(4789,1)]')]
    assert seeds == [(0,12,10,8517),(1,17,16,8522),(2,15,13,8528),(3,21,20,8533)]
    source = f'''import ShielddSecurity.{HASH}
import ShielddSecurity.{FIELD}
set_option maxHeartbeats 600000
namespace ShielddSecurity.{NAME}
variable {{F Q Encoded : Type}} [Field F] [CharP F Scalar.modulus]
variable (hex : TransferEncryptionSdkShielddNativeParameterBytes.HexCodec Encoded)
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : TransferEncryptionSdkShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : TransferEncryptionSdkShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)
def addPad (rho : Nat → F) (call : Nat) (plaintext : F) : Option Q :=
  ({HASH}.nativeCall hex fq arithmetic initial square codec rho call).map
    (fun pad => arithmetic.add (ShielddNativeIvkHash.sdkConstant fq arithmetic codec plaintext) pad)
def sumHashes (rho : Nat → F) (left right : Nat) : Option Q :=
  ({HASH}.nativeCall hex fq arithmetic initial square codec rho left).bind (fun plain =>
    ({HASH}.nativeCall hex fq arithmetic initial square codec rho right).map
      (fun pad => arithmetic.add plain pad))
private theorem hash_rows (rho : Nat → F) (satisfied : Satisfies rho {FIELD}.rawRows) :
    Satisfies rho {GRAPH}.rawRows := by
  intro row inside
  exact satisfied row (List.mem_append_left _ inside)
private theorem hash_value (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) (call : Fin 24) :
    ({HASH}.nativeCall hex fq arithmetic initial square codec rho call.val).map
      (ShielddNativeIvkHash.fqValue (F := F) fq) = some ({FIELD}.hashValue rho call.val) := by
  have rows := {GRAPH}.all_hashes_sound rho one (hash_rows rho satisfied) call
  simpa only [rows, {FIELD}.hashValue] using
    {HASH}.call_value hex fq arithmetic initial square codec rho one (hash_rows rho satisfied) call
private theorem add_pad_value (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) (call : Fin 24) (plaintext : F) :
    (addPad hex fq arithmetic initial square codec rho call.val plaintext).map
      (ShielddNativeIvkHash.fqValue (F := F) fq) = some (plaintext + {FIELD}.hashValue rho call.val) := by
  have value := hash_value hex fq arithmetic initial square codec rho one satisfied call
  cases parsed : {HASH}.nativeCall hex fq arithmetic initial square codec rho call.val with
  | none => simp only [parsed, Option.map_none] at value; cases value
  | some pad =>
    have meaning : ShielddNativeIvkHash.fqValue (F := F) fq pad = {FIELD}.hashValue rho call.val := by
      simpa only [parsed, Option.map_some, Option.some.injEq] using value
    simp only [addPad, parsed, Option.map_some, arithmetic.addValue,
      ShielddNativeIvkHash.sdk_constant_value, meaning]
private theorem sum_hashes_value (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) (left right : Fin 24) :
    (sumHashes hex fq arithmetic initial square codec rho left.val right.val).map
      (ShielddNativeIvkHash.fqValue (F := F) fq) =
      some ({FIELD}.hashValue rho left.val + {FIELD}.hashValue rho right.val) := by
  have leftValue := hash_value hex fq arithmetic initial square codec rho one satisfied left
  have rightValue := hash_value hex fq arithmetic initial square codec rho one satisfied right
  cases leftParsed : {HASH}.nativeCall hex fq arithmetic initial square codec rho left.val with
  | none => simp only [leftParsed, Option.map_none] at leftValue; cases leftValue
  | some plain =>
    have plainValue : ShielddNativeIvkHash.fqValue (F := F) fq plain = {FIELD}.hashValue rho left.val := by
      simpa only [leftParsed, Option.map_some, Option.some.injEq] using leftValue
    cases rightParsed : {HASH}.nativeCall hex fq arithmetic initial square codec rho right.val with
    | none => simp only [rightParsed, Option.map_none] at rightValue; cases rightValue
    | some pad =>
      have padValue : ShielddNativeIvkHash.fqValue (F := F) fq pad = {FIELD}.hashValue rho right.val := by
        simpa only [rightParsed, Option.map_some, Option.some.injEq] using rightValue
      simp only [sumHashes, leftParsed, rightParsed, Option.bind_some,
        Option.map_some, arithmetic.addValue, plainValue, padValue]
/-- Generic canonical conversion; public cipher lemmas derive its field premise
from actual rows and native programs rather than accepting that premise. -/
private theorem integer_of_value (result : Option Q) (expected : F)
    (value : result.map (ShielddNativeIvkHash.fqValue (F := F) fq) = some expected) :
    result.map fq.integer = some (codec.decode expected) := by
  cases result with
  | none => simp only [Option.map_none] at value; cases value
  | some native =>
    have meaning : ShielddNativeIvkHash.fqValue (F := F) fq native = expected := by
      simpa only [Option.map_some, Option.some.injEq] using value
    have decoded : fq.integer native = codec.decode expected := by
      rw [← meaning]
      exact (TransferReduction.decode_canonical_cast codec (fq.integer native) (fq.bounded native)).symm
    simpa only [Option.map_some] using congrArg some decoded
'''
    roles = []
    for name, call, plain in cases:
        if name == 'detection1':
            expression = f'sumHashes hex fq arithmetic initial square codec rho 0 {call}'
            proof = f'sum_hashes_value hex fq arithmetic initial square codec rho one satisfied ⟨0,by decide⟩ ⟨{call},by decide⟩'
        elif plain is None:
            expression = f'{HASH}.nativeCall hex fq arithmetic initial square codec rho {call}'
            proof = f'hash_value hex fq arithmetic initial square codec rho one satisfied ⟨{call},by decide⟩'
        else:
            plaintext = '0' if plain == '[]' else f'(eval rho {plain})'
            expression = f'addPad hex fq arithmetic initial square codec rho {call} {plaintext}'
            proof = f'add_pad_value hex fq arithmetic initial square codec rho one satisfied ⟨{call},by decide⟩ {plaintext}'
        roles.append((name, name, expression, proof, name+'_sound', plain=='[]'))
    for tier, _, secret, _ in seeds:
        name = f'c2_{tier}'
        expression = f'addPad hex fq arithmetic initial square codec rho {secret} ({FIELD}.seed{tier} rho)'
        proof = f'add_pad_value hex fq arithmetic initial square codec rho one satisfied ⟨{secret},by decide⟩ ({FIELD}.seed{tier} rho)'
        roles.append((name, name, expression, proof, f'c2_seed{tier}_sound', False))
    exports = []
    for name, field, expression, proof, rows, zero in roles:
        source += f'''/-- Owned arithmetic on canonical input images. Actual caller object
and DH/EPK operand/source bindings are separate, not supplied as conclusions. -/
def {name} (rho : Nat → F) : Option Q := {expression}
theorem {name}_value (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    ({name} hex fq arithmetic initial square codec rho).map
      (ShielddNativeIvkHash.fqValue (F := F) fq) = some (eval rho {FIELD}.{field}) := by
  have native := {proof}
  rw [{FIELD}.{rows} rho one satisfied]
'''
        source += f'  simpa only [{name}' + (', zero_add' if zero else '') + '] using native\n'
        source += f'''theorem {name}_integer (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    ({name} hex fq arithmetic initial square codec rho).map fq.integer =
      some (codec.decode (eval rho {FIELD}.{field})) :=
  integer_of_value fq codec _ _ ({name}_value hex fq arithmetic initial square codec rho one satisfied)
'''
        exports.extend([f'ShielddSecurity.{NAME}.{name}_value', f'ShielddSecurity.{NAME}.{name}_integer'])
    source += f'end ShielddSecurity.{NAME}\n'
    source += ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n' for name in exports)
    assert len(exports) == 24
    assert re.findall(r'^#check @([\w.]+)$', source, re.M) == exports
    assert re.findall(r'^#print axioms ([\w.]+)$', source, re.M) == exports
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source)
    return source, exports
