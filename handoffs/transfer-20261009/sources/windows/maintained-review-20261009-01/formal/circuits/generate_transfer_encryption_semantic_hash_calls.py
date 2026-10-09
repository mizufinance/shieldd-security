"""Derive semantic input lists for the actual twenty-four encryption hashes.

Four small groups keep source-expression normalization separate from hash
soundness. DH/EPK coordinates are actual row expressions; their group and
caller interpretations remain separate obligations.
"""
import re

GRAPH = 'RuntimeTransferEncryptionHashGraph'
FIELD = 'RuntimeTransferEncryptionFieldCipherGraph'
NATURAL = 'TransferEncryptionNaturalHashGraph'
DOMAINS = [14]*5 + [12] + [10]*4 + [11,13,10,11,13,10,11,10,10,10,11,10,10,10]
MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
SEED_CALLS = {0:12, 1:17, 2:15, 3:21}


def model(call):
    column = lambda value: ('column', value)
    constant = lambda value: ('constant', value)
    seed = lambda tier: ('seed', tier)
    hashed = lambda index: ('hash', index)
    if call < 5:
        return [column(8), constant(call)]
    if call == 5:
        return list(map(column, [13627,13628,8515,8516]))
    if 6 <= call <= 9:
        return [hashed(5), constant(call-6)]
    if call in (10,13,16,20):
        x = {10:12871,13:16151,16:14889,20:17413}[call]
        return [column(x), column(x+1)]
    if call in (11,14):
        tier, x, salt = {11:(0,8515,1),14:(2,8526,3)}[call]
        return [seed(tier), column(x), column(x+1), hashed(salt)]
    if call in (12,15):
        return [seed({12:0,15:2}[call]), constant(0)]
    if 17 <= call <= 19:
        return [seed(1), constant(call-17)]
    assert 21 <= call <= 23
    return [seed(3), constant(call-21)]


def canonical(linear):
    result = {}
    for column, coefficient in linear:
        assert isinstance(column, int) and column >= 0 and isinstance(coefficient, int)
        result[column] = (result.get(column, 0) + coefficient) % MODULUS
    return sorted((column, value) for column, value in result.items() if value)


def linear_text(linear):
    return '[' + ', '.join(f'({column}, ({coefficient} : Int))' for column,coefficient in linear) + ']'


def expected(records, node):
    kind, value = node
    if kind == 'column':
        return [(value,1)]
    if kind == 'constant':
        return [(0,value)]
    if kind == 'hash':
        return records[value]['output']
    assert kind == 'seed'
    return records[SEED_CALLS[value]]['inputs'][0]


def field_term(node):
    kind, value = node
    if kind == 'column':
        return f'eval rho [({value},1)]'
    if kind == 'constant':
        return f'({value} : F)'
    if kind == 'hash':
        return f'{FIELD}.hashValue rho {value}'
    assert kind == 'seed'
    return f'{FIELD}.seed{value} rho'


def natural_term(node):
    return str(node[1]) if node[0] == 'constant' else f'codec.decode ({field_term(node)})'


def generate(records):
    assert len(records) == 24
    for tier, (column, secret) in enumerate([(8517,10),(8522,16),(8528,13),(8533,20)]):
        recovered = [(column,1)] + [(index,-coefficient) for index,coefficient in records[secret]['output']]
        assert canonical(records[SEED_CALLS[tier]]['inputs'][0]) == canonical(recovered), tier
    for call, record in enumerate(records):
        assert record['call'] == call and record['domain'] == DOMAINS[call]
        nodes = model(call)
        assert len(record['inputs']) == len(nodes)
        for actual, node in zip(record['inputs'], nodes):
            assert canonical(actual) == canonical(expected(records,node)), (call,node)
    modules = {}
    for group in range(4):
        name = f'TransferEncryptionSemanticHashCalls{group}'
        source = f'''import ShielddSecurity.{NATURAL}
set_option maxHeartbeats 600000
namespace ShielddSecurity.{name}
variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
'''
        exports = []
        for call in range(group*6,(group+1)*6):
            record = records[call]
            nodes = model(call)
            values = '[' + ', '.join(field_term(node) for node in nodes) + ']'
            naturals = '[' + ', '.join(natural_term(node) for node in nodes) + ']'
            source += f'''theorem call{call}_inputs_field (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {GRAPH}.rawRows) :
    ({GRAPH}.inputs {call}).map (eval rho) = {values} := by
'''
            for index, (actual, node) in enumerate(zip(record['inputs'],nodes)):
                kind, value = node
                literal, normalized = linear_text(actual), linear_text(expected(records,node))
                source += f'  have input{index} : eval rho {literal} = {field_term(node)} := by\n'
                if kind in ('column','seed'):
                    source += f'''    change eval rho {literal} = eval rho {normalized}
    exact Compiler.canonical_equal rho _ _ (by decide)
'''
                else:
                    endpoint = f'{GRAPH}.output {value}' if kind == 'hash' else normalized
                    source += f'''    calc
      _ = eval rho ({endpoint}) := Compiler.canonical_equal rho _ _ (by decide)
'''
                    if kind == 'constant':
                        source += f'      _ = ({value} : F) := by norm_num [eval, one]\n'
                    else:
                        source += f'''      _ = {FIELD}.hashValue rho {value} := by
        simpa only [{FIELD}.hashValue] using
          {GRAPH}.all_hashes_sound rho one satisfied ⟨{value},by decide⟩
'''
            actuals = '[' + ', '.join(f'eval rho {linear_text(arg)}' for arg in record['inputs']) + ']'
            source += f'  change {actuals} = {values}\n'
            source += '  rw [' + ', '.join(f'input{i}'for i in range(len(nodes))) + ']\n'
            source += f'''theorem call{call}_inputs_natural (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {GRAPH}.rawRows) :
    {NATURAL}.naturalInputs codec rho {call} = {naturals} := by
  have decoded := congrArg (List.map codec.decode) (call{call}_inputs_field rho one satisfied)
'''
            constants = sorted({value for kind,value in nodes if kind == 'constant'})
            for value in constants:
                source += f'''  have constant{value} : codec.decode ({value} : F) = {value} := by
    simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
      (TransferReduction.decode_canonical_cast codec {value} (by decide))
'''
            rules = [f'{NATURAL}.naturalInputs','List.map_map','Function.comp_def',
                     'List.map_cons','List.map_nil',*[f'constant{value}'for value in constants]]
            source += '  simpa only [' + ', '.join(rules) + '] using decoded\n'
            source += f'''theorem call{call}_hash_natural (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {GRAPH}.rawRows) :
    codec.decode (eval rho ({GRAPH}.output {call})) =
      {NATURAL}.naturalHash codec {record['domain']} {naturals} := by
  simpa only [TransferEncryptionNativeHashGraph.domain,
    call{call}_inputs_natural codec rho one satisfied] using
    {NATURAL}.all_hashes_natural codec rho one satisfied ⟨{call},by decide⟩
'''
            exports += [f'ShielddSecurity.{name}.call{call}_{suffix}'
                        for suffix in ('inputs_field','inputs_natural','hash_natural')]
        source += f'end ShielddSecurity.{name}\n'
        source += ''.join(f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
                          for export in exports)
        assert len(exports) == 18
        assert re.findall(r'^#check @([\w.]+)$',source,re.M) == exports
        assert re.findall(r'^#print axioms ([\w.]+)$',source,re.M) == exports
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source)
        modules[name] = source
    return modules
