"""Adversarial field assignments for the exact selected arithmetic slice."""
from controls import satisfies
from generate import P
from volume_rows import BOUND, select


def check(export):
    selected = select(export)
    blocks, variables = selected['blocks'], selected['variables']
    rows = [row for block in blocks.values() for row in block]

    def assignment(a, b, s, limit, real, borrow, difference, candidate_bits):
        values = [a, s, b, limit, real, borrow, difference]
        rho = {0: 1, **dict(zip(variables, values))}
        bit_values = [b, a, s, candidate_bits, limit, difference % BOUND]
        for columns, value in zip(selected['bits'], bit_values):
            rho.update({column: (value >> i) & 1 for i, column in enumerate(columns)})
        for name, x, y in [('successor_gate', real, s-a-b), ('limit_gate', real, borrow)]:
            gate = selected['gates'][name]
            rho[gate['difference']] = (x-y)**2 % P
            rho[gate['output']] = x*y % P
        return rho

    cases = [
        ('padding candidate overflow', assignment(BOUND-1, 1, 0, 0, 0, 0, 0, 0), blocks['candidate'][-1]),
        ('unbounded comparison difference', assignment(1, 0, 1, 0, 1, 0, P-1, 1), blocks['difference'][-1]),
    ]
    result = []
    for name, rho, removed in cases:
        weakened = [row for row in rows if row['index'] != removed['index']]
        if satisfies({'rows': rows}, rho) or not satisfies({'rows': weakened}, rho):
            raise ValueError(f'{name}: intended original rejection/weakened acceptance not observed')
        result.append({'case': name, 'removed_original_row': removed['index'],
                       'original': 'rejected', 'weakened': 'accepted'})
    return {'scope': 'precise arithmetic slice; no assertion that arbitrary values extend through surrounding crypto',
            'arbitrary_assignment_controls': result}
