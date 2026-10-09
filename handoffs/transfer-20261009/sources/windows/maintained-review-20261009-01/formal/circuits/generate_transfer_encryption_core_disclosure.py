"""Compose actual encryption hash, recovered seed and core cipher equations.

Coordinate values are read from actual columns. Group multiplication and
native caller correspondence must be proved separately before full semantics.
"""
import re
from circuits.generate_transfer_encryption_semantic_hash_calls import model, DOMAINS

NAME = 'TransferEncryptionCoreDisclosure'
GRAPH = 'RuntimeTransferEncryptionHashGraph'
FIELD = 'RuntimeTransferEncryptionFieldCipherGraph'
NATURAL = 'TransferEncryptionNaturalHashGraph'
CIPHER = 'TransferEncryptionNaturalCipherGraph'
SEED = 'TransferEncryptionNaturalSeedGraph'
SECRET_CALL = {0:10, 1:16, 2:13, 3:20}
C2 = {0:8517, 1:8522, 2:8528, 3:8533}


def value(call):
    if call < 5:
        return f'salt codec rho {call}'
    if call == 5:
        return 'detectionSeed codec rho'
    if call in SECRET_CALL.values():
        tier = next(tier for tier,index in SECRET_CALL.items() if index == call)
        return f'secret codec rho {tier}'
    return f'{NATURAL}.naturalHash codec {DOMAINS[call]} ' + '[' + ', '.join(term(node) for node in model(call)) + ']'


def term(node):
    kind, index = node
    if kind == 'column': return f'word codec rho {index}'
    if kind == 'constant': return str(index)
    if kind == 'seed': return f'seed codec rho {index}'
    assert kind == 'hash'
    return value(index)


def generate():
    source = ''.join(f'import ShielddSecurity.TransferEncryptionSemanticHashCalls{i}\n' for i in range(4))
    source += f'''import ShielddSecurity.{CIPHER}
import ShielddSecurity.{SEED}
set_option maxHeartbeats 600000
namespace ShielddSecurity.{NAME}
variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
variable (codec : TransferReduction.CanonicalField F)

-- Compose named equations without definitionally expanding the full recipes.
attribute [local irreducible] {FIELD}.hashValue {NATURAL}.naturalHash
attribute [local irreducible] {FIELD}.seed0 {FIELD}.seed1 {FIELD}.seed2 {FIELD}.seed3

def word (rho : Nat → F) (column : Nat) : Nat := codec.decode (eval rho [(column,1)])
def salt (rho : Nat → F) (slot : Nat) : Nat :=
  {NATURAL}.naturalHash codec 14 [word codec rho 8, slot]
def detectionSeed (rho : Nat → F) : Nat :=
  {NATURAL}.naturalHash codec 12
    [word codec rho 13627, word codec rho 13628, word codec rho 8515, word codec rho 8516]
def secret (rho : Nat → F) (tier : Nat) : Nat :=
  let x := match tier with | 0 => 12871 | 1 => 14889 | 2 => 16151 | _ => 17413
  {NATURAL}.naturalHash codec 11 [word codec rho x, word codec rho (x+1)]
def seed (rho : Nat → F) (tier : Nat) : Nat :=
  let column := match tier with | 0 => 8517 | 1 => 8522 | 2 => 8528 | _ => 8533
  {SEED}.subtractNat (word codec rho column) (secret codec rho tier)

private theorem hash_rows (rho : Nat → F)
    (satisfied : Satisfies rho {FIELD}.rawRows) : Satisfies rho {GRAPH}.rawRows := by
  intro row inside
  exact satisfied row (List.mem_append_left _ inside)

private theorem hash_value_output (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) (call : Fin 24) :
    {FIELD}.hashValue rho call.val = eval rho ({GRAPH}.output call.val) := by
  simpa only [{FIELD}.hashValue] using
    ({GRAPH}.all_hashes_sound rho one (hash_rows rho satisfied) call).symm
'''
    exports = []
    for call in range(24):
        raw = '[' + ', '.join(str(index) if kind == 'constant' else
            f'codec.decode (eval rho [({index},1)])' if kind == 'column' else
            f'codec.decode ({FIELD}.seed{index} rho)' if kind == 'seed' else
            f'codec.decode ({FIELD}.hashValue rho {index})' for kind,index in model(call)) + ']'
        group = call // 6
        deps = [f'h{index} codec rho one satisfied' if kind == 'hash' else
                f'seed{index}_semantic codec rho one satisfied' for kind,index in model(call) if kind in ('hash','seed')]
        rules = ['word','salt','secret','detectionSeed',*deps]
        source += f'''
private theorem h{call} (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    codec.decode ({FIELD}.hashValue rho {call}) = {value(call)} := by
  have computed : codec.decode ({FIELD}.hashValue rho {call}) =
      {NATURAL}.naturalHash codec {DOMAINS[call]} {raw} := by
    calc
      _ = codec.decode (eval rho ({GRAPH}.output {call})) :=
        congrArg codec.decode (hash_value_output rho one satisfied ⟨{call},by decide⟩)
      _ = _ := TransferEncryptionSemanticHashCalls{group}.call{call}_hash_natural codec rho one (hash_rows rho satisfied)
  simpa only [{', '.join(rules)}] using computed
'''
        if call in SECRET_CALL.values():
            tier = next(tier for tier,index in SECRET_CALL.items() if index == call)
            source += f'''
theorem seed{tier}_semantic (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    codec.decode ({FIELD}.seed{tier} rho) = seed codec rho {tier} := by
  change codec.decode ({FIELD}.seed{tier} rho) =
    {SEED}.subtractNat (codec.decode (eval rho [({C2[tier]},1)])) (secret codec rho {tier})
  have recovered := {SEED}.seed{tier}_natural codec rho one satisfied
  rw [h{call} codec rho one satisfied] at recovered
  exact recovered
'''
            exports.append(f'ShielddSecurity.{NAME}.seed{tier}_semantic')
    cases = [
        ('detection0', f'{CIPHER}.addNat (word codec rho 6) ({value(6)})', [6]),
        ('detection1', f'{CIPHER}.addNat (salt codec rho 0) ({value(7)})', [0,7]),
        ('detection2', f'{CIPHER}.addNat (word codec rho 108486) ({value(8)})', [8]),
        ('detection3', value(9), [9]),
        ('core0_confirmation', value(11), [11]),
        ('core0_amount', f'{CIPHER}.addNat (word codec rho 4789) ({value(12)})', [12]),
        ('core2_confirmation', value(14), [14]),
        ('core2_amount', f'{CIPHER}.addNat (word codec rho 4789) ({value(15)})', [15]),
    ]
    for name,rhs,calls in cases:
        rules = [f'{CIPHER}.hashNat','word',*[f'h{call} codec rho one satisfied' for call in calls]]
        source += f'''
theorem {name}_semantic (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    {CIPHER}.ciphertext codec rho {FIELD}.{name} = {rhs} := by
  simpa only [{', '.join(rules)}] using
    {CIPHER}.{name}_natural codec rho one satisfied
'''
        exports.append(f'ShielddSecurity.{NAME}.{name}_semantic')
    source += f'end ShielddSecurity.{NAME}\n'
    source += ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n' for name in exports)
    assert len(exports) == 12 and len(set(exports)) == 12
    assert re.findall(r'^#check @([\w.]+)$',source,re.M) == exports
    assert re.findall(r'^#print axioms ([\w.]+)$',source,re.M) == exports
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    return source,exports
