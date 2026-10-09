"""Bridge captured encryption hash rows to canonical native field objects.

This does not identify caller objects with these canonical images. That source
and caller obligation stays separate from the arbitrary-row value theorem.
"""
import re

NAME = 'TransferEncryptionNativeHashGraph'
GRAPH = 'RuntimeTransferEncryptionHashGraph'
GROUP = 'RuntimeTransferEncryptionHashGroup0'
LOADED = 'TransferEncryptionSdkShielddNativeFieldHashLoaded'


def cases24(target):
    choices = ' ∨ '.join(f'index = {i}' for i in range(24))
    return (f'  rcases call with ⟨index, bound⟩\n'
            f'  change {target}\n'
            f'  have choices : {choices} := by omega\n'
            '  rcases choices with ' + ' | '.join(['rfl']*24) + '\n')


def generate(records):
    assert len(records) == 24
    for call, record in enumerate(records):
        assert record['call'] == call
        assert record['width'] == (6 if call in (5, 11, 14) else 3)
        assert 0 <= record['domain'] < 256
    source = f'''import ShielddSecurity.{GRAPH}
import ShielddSecurity.{LOADED}
set_option maxHeartbeats 600000
namespace ShielddSecurity.{NAME}
def domain (call : Nat) : Nat := match call with
'''
    source += ''.join(f'  | {r["call"]} => {r["domain"]}\n' for r in records)
    source += '''  | _ => 0
def arity (call : Nat) : Nat := match call with
  | 5 => 4
  | 11 => 4
  | 14 => 4
  | _ => 2
theorem inputs_length (call : Fin 24) :
    (RuntimeTransferEncryptionHashGraph.inputs call.val).length = arity call.val := by
'''
    source += cases24(f'({GRAPH}.inputs index).length = arity index') + ''.join('  · rfl\n' for _ in records)
    source += '''theorem iv_bound (call : Fin 24) :
    arity call.val * 256 + domain call.val < 2^64 := by
'''
    source += cases24('arity index * 256 + domain index < 2^64') + ''.join('  · decide\n' for _ in records)
    source += f'''variable {{F Q Encoded : Type}} [Field F] [CharP F Scalar.modulus]
variable (hex : TransferEncryptionSdkShielddNativeParameterBytes.HexCodec Encoded)
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : TransferEncryptionSdkShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : TransferEncryptionSdkShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)
/-- Canonical native images of the actual captured input expressions. Actual
caller objects and their source bindings are a separate obligation. -/
def nativeInputs (rho : Nat → F) (call : Nat) : List Q :=
  ({GRAPH}.inputs call).map (fun input =>
    ShielddNativeIvkHash.sdkConstant fq arithmetic codec (eval rho input))
def nativeCall (rho : Nat → F) (call : Nat) : Option Q :=
  {LOADED}.loadedHash hex fq arithmetic initial square (domain call)
    (nativeInputs fq arithmetic codec rho call)
theorem inputs_value (rho : Nat → F) (call : Nat) :
    (nativeInputs fq arithmetic codec rho call).map (ShielddNativeIvkHash.fqValue (F := F) fq) =
      ({GRAPH}.inputs call).map (eval rho) := by
  simp only [nativeInputs, List.map_map, Function.comp_def,
    ShielddNativeIvkHash.sdk_constant_value]
theorem recipe (call : Fin 24) (values : List F) (length : values.length = arity call.val) :
    {GRAPH}.hashAt call.val values = Poseidon.hash
      (Poseidon.castParameters {GROUP}.smallRecipe)
      (Poseidon.castParameters {GROUP}.wideRecipe) (domain call.val) values := by
'''
    source += cases24(f'{GRAPH}.hashAt index values = Poseidon.hash '
                      f'(Poseidon.castParameters {GROUP}.smallRecipe) '
                      f'(Poseidon.castParameters {GROUP}.wideRecipe) (domain index) values')
    for r in records:
        width, domain = r['width'], r['domain']
        recipe = 'wideRecipe' if width == 6 else 'smallRecipe'
        n = 4 if width == 6 else 2
        condition = 'if_neg' if width == 6 else 'if_pos'
        comparison = '¬ values.length ≤ 2' if width == 6 else 'values.length ≤ 2'
        source += f'''  · change Poseidon.hash{width} (Poseidon.castParameters {GROUP}.{recipe}) {domain} values =
      Poseidon.hash (Poseidon.castParameters {GROUP}.smallRecipe)
        (Poseidon.castParameters {GROUP}.wideRecipe) {domain} values
    have exactLength : values.length = {n} := length
    rw [Poseidon.hash, {condition} (by omega : {comparison})]
'''
    source += f'''/-- Actual row soundness plus the owned loaded-parameter consumer, with only
global primitive contracts. No hash result, table equality or honest witness
is supplied as a premise. -/
theorem call_value (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {GRAPH}.rawRows) (call : Fin 24) :
    (nativeCall hex fq arithmetic initial square codec rho call.val).map
      (ShielddNativeIvkHash.fqValue (F := F) fq) =
      some (eval rho ({GRAPH}.output call.val)) := by
  have length : (nativeInputs fq arithmetic codec rho call.val).length = arity call.val := by
    simp only [nativeInputs, List.length_map, inputs_length]
  have bounded : (nativeInputs fq arithmetic codec rho call.val).length * 256 + domain call.val < 2^64 := by
    rw [length]
    exact iv_bound call
  have native := {LOADED}.hash_value hex fq arithmetic initial square codec
    (domain call.val) (nativeInputs fq arithmetic codec rho call.val) bounded
  rw [inputs_value fq arithmetic codec rho call.val] at native
  have rows := {GRAPH}.all_hashes_sound rho one satisfied call
  rw [recipe call _ (by simpa only [List.length_map] using inputs_length call)] at rows
  change _ = some _
  simpa only [nativeCall, TransferEncryptionSdkNativeAssetHashParameters.smallParameters,
    {LOADED}.wideParameters, rows] using native
/-- Equality of canonical integers follows from Fq bounds and the canonical
field codec, rather than being assumed from a successful native callback. -/
theorem call_integer (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {GRAPH}.rawRows) (call : Fin 24) :
    (nativeCall hex fq arithmetic initial square codec rho call.val).map fq.integer =
      some (codec.decode (eval rho ({GRAPH}.output call.val))) := by
  have value := call_value hex fq arithmetic initial square codec rho one satisfied call
  cases result : nativeCall hex fq arithmetic initial square codec rho call.val with
  | none => simp only [result, Option.map_none, reduceCtorEq] at value
  | some native =>
    have fieldValue : ShielddNativeIvkHash.fqValue (F := F) fq native =
        eval rho ({GRAPH}.output call.val) := by
      simpa only [result, Option.map_some, Option.some.injEq] using value
    have integerValue : fq.integer native = codec.decode (eval rho ({GRAPH}.output call.val)) := by
      rw [← fieldValue]
      exact (TransferReduction.decode_canonical_cast codec (fq.integer native) (fq.bounded native)).symm
    simpa only [result, Option.map_some] using congrArg some integerValue
end ShielddSecurity.{NAME}
'''
    exports = [f'ShielddSecurity.{NAME}.{name}' for name in
               ['inputs_length', 'iv_bound', 'inputs_value', 'recipe', 'call_value', 'call_integer']]
    source += ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n' for name in exports)
    assert re.findall(r'^#check @([\w.]+)$', source, re.M) == exports
    assert re.findall(r'^#print axioms ([\w.]+)$', source, re.M) == exports
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source)
    return source, exports
