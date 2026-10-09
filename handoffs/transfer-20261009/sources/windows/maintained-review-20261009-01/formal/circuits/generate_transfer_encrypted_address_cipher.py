"""Derive the six extended ciphertext assertions from retained ordinary rows."""
from .generate_hash_round import linear
from .transfer_balance_rows import canonical, combine
from .transfer_encryption_address_rows import SCHEMA
from .transfer_relation import MODULUS


def generate(extraction):
    assert extraction['schema'] == SCHEMA
    plan = extraction['plan']
    rows = {item['row']: item for item in extraction['selected_rows']}
    link = rows[plan['constant_link']]
    assert link['b'] == [] and len(link['a']) == 2
    actual = tuple((column, int(value, 16)) for column, value in link['a'])
    assert actual[0] == (0, 1) and actual[1][1] == MODULUS - 1
    copy = actual[1][0]
    assert copy != 0
    result = {}
    for address in plan['addresses']:
        assert address['owner'] in ['Receiver', 'Sender']
        name = 'RuntimeEncryptionAddress' + address['owner'] + 'CipherRows'
        words = address['words']
        assert [word['ordinal'] for word in words] == [0, 1, 2]
        indices = [plan['constant_link']] + [word['assertion_row'] for word in words]
        assert len(set(indices)) == 4
        raw = {index: tuple(tuple((column, int(value, 16)) for column, value in rows[index][side])
                            for side in ['a', 'b']) for index in indices}
        normalized = {index: tuple(canonical((0 if column == copy else column, value)
                                             for column, value in side) for side in row)
                      for index, row in raw.items()}
        # The retained 31-byte word has 248 weighted LC terms. Keep the
        # heartbeat budget finite while allowing its bounded list certificate
        # to elaborate without Lean's default recursion-depth cutoff.
        text = ('import ShielddSecurity.ScalarBits\nset_option maxHeartbeats 400000\n'
                'set_option maxRecDepth 4096\n'
                f'namespace ShielddSecurity.{name}\n'
                f'def modulus : Nat := {MODULUS}\n'
                'def rawRows : List Row := [\n' + ',\n'.join(
                    '⟨' + linear(a) + ',' + linear(b) + '⟩' for a, b in raw.values()) + ']\n'
                f'def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n'
                f'theorem constant_link : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n')
        exports = ['constant_link']
        for word in words:
            ordinal = word['ordinal']
            left, stream, packed = [canonical(word[key]) for key in ['output', 'stream', 'word']]
            right = combine(stream, packed)
            delta = combine(left, right, -1)
            actual_row = normalized[word['assertion_row']]
            direct = actual_row == (delta, ())
            assert direct or actual_row == (canonical((column, -value) for column, value in delta), ())
            first, second = (left, right) if direct else (right, left)
            proof = (f'Compiler.checked_assertion_sound rho rows {linear(first)} {linear(second)} '
                     'normalized (by decide)')
            if not direct:
                proof = '(' + proof + ').symm'
            text += f'''theorem cipher{ordinal} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(left)} = eval rho {linear(stream)} + eval rho {linear(packed)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constant_link
  have asserted := {proof}
  have operands := Compiler.canonical_equal rho {linear(right)}
    ({linear(stream)} ++ {linear(packed)}) (by decide)
  exact asserted.trans (operands.trans (eval_append rho _ _))
'''
            columns = word['columns']
            assert len(columns) == (248 if ordinal < 2 else 16)
            assert packed == canonical((column, 2 ** bit) for bit, column in enumerate(columns))
            bits = '[' + ','.join(linear([(column, 1)]) for column in columns) + ']'
            text += f'''def bits{ordinal} : List Linear := {bits}
theorem word{ordinal} {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    eval rho {linear(packed)} = eval rho (ScalarBits.bitLinear bits{ordinal}) := by
  exact Compiler.canonical_equal rho {linear(packed)}
    (ScalarBits.bitLinear bits{ordinal}) (by decide)
'''
            exports += [f'cipher{ordinal}', f'word{ordinal}']
        assert len(exports) == 7
        for export in exports:
            text += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        text += f'end ShielddSecurity.{name}\n'
        result[name] = text
    assert len(result) == 2
    return result
