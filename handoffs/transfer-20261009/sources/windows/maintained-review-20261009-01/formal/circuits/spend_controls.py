"""Adversarial assignments to the actual spend slice, not typed Rust witnesses.

Each underconstraint control accepts the explicit bad field assignment only
after the intended selected row is weakened. This is finite qualification of
the slice/checker, not a claim that the whole Transfer accepts that assignment.
"""
from copy import deepcopy
from generate import P
from spend_rows import select


def evaluate(terms, rho):
    return sum(coefficient * rho.get(column, 0) for column, coefficient in terms) % P


def rows_of(selected):
    return {row['index']: row for block in selected['blocks'].values() for row in block}


def satisfied(rows, rho):
    for row in rows.values():
        a = evaluate([(i, int(c, 16)) for i, c in row['a']], rho)
        b = evaluate([(i, int(c, 16)) for i, c in row['b']], rho)
        if a * a % P != b:
            return False
    return True


def assignment(selected, *, amount=(7, 5), position=(8, 12), floor=10, dummy=0,
               nullifiers=None, real_nullifiers=(17, 19), synthetic=23,
               roots=(29, 29), anchor=29, borrow=None):
    def column(role):
        return selected['observations'][role]['linear'][0][0]

    rho = {0: 1, selected['outline']: 1}
    if borrow is None:
        borrow = tuple(int(pos < floor) for pos in position)
    if nullifiers is None:
        nullifiers = (real_nullifiers[0], dummy * synthetic + (1 - dummy) * real_nullifiers[1])
    for slot in [0, 1]:
        values = {'amount': amount[slot], 'position': position[slot], 'floor': floor,
                  'borrow': borrow[slot], 'difference': (position[slot] - floor + borrow[slot] * 2**48) % P,
                  'anchor': anchor, 'nullifier': nullifiers[slot],
                  'history': borrow[slot] * (1 if slot == 0 else 1 - dummy)}
        for role, value in values.items():
            rho[column(f'spend{slot}.{role}')] = value % P
        for role in ['amount', 'position', 'floor', 'difference']:
            for i, bit in enumerate(selected['bits'][f'spend{slot}.{role}']):
                rho[bit] = (values[role] >> i) & 1
    rho[column('spend1.dummy')] = dummy
    for role, target in [('spend0.real_nullifier', real_nullifiers[0]), ('spend1.real_nullifier', real_nullifiers[1]),
                         ('spend0.computed_root', roots[0]), ('spend1.computed_root', roots[1]),
                         ('spend1.synthetic_nullifier', synthetic)]:
        terms = selected['observations'][role]['linear']
        for column_, _ in terms:
            rho[column_] = 0
        pivot, coefficient = terms[0]
        rho[pivot] = target * pow(coefficient % P, -1, P) % P
    for gate in selected['gates'].values():
        x, y = evaluate(gate['x'], rho), evaluate(gate['y'], rho)
        rho[gate['difference']] = (x - y) ** 2 % P
        rho[gate['output']] = x * y % P
    return rho


def check(export):
    selected = select(export)
    rows = rows_of(selected)
    positives = [
        assignment(selected),
        assignment(selected, amount=(0, 0), position=(10, 10)),
        assignment(selected, amount=(2**128 - 1, 0), position=(0, 2**48 - 1), dummy=1),
    ]
    if not all(satisfied(rows, rho) for rho in positives):
        raise AssertionError('legal arithmetic/branch assignment rejected by exact selected rows')
    extensions = 0
    fresh = set(selected['extension_columns'])
    for legal in positives:
        base = dict(legal)
        # Preserve otherwise unrelated public/committed data as well as actual
        # semantic/hash supports; overwrite only the declared tail ownership.
        base[1], base[2] = 123456, 654321
        for i in fresh:
            base[i] = (37 * i + 11) % P
        extended = dict(base)
        for slot in [0, 1]:
            column = lambda role: selected['observations'][f'spend{slot}.{role}']['linear'][0][0]
            position, floor = base[column('position')], base[column('floor')]
            borrow = int(position < floor)
            difference = position - floor + borrow * 2**48
            extended[column('borrow')] = borrow
            extended[column('difference')] = difference
            for index, bit in enumerate(selected['bits'][f'spend{slot}.difference']):
                extended[bit] = (difference >> index) & 1
        for gate in selected['gates'].values():
            x, y = evaluate(gate['x'], extended), evaluate(gate['y'], extended)
            extended[gate['difference']] = (x-y)**2 % P
            extended[gate['output']] = x*y % P
        if not satisfied(rows, extended):
            raise AssertionError('tail extension failed exact selected rows')
        if any(extended[i] != value for i, value in base.items() if i not in fresh):
            raise AssertionError('tail extension overwrote surrounding assignment')
        extensions += 1
    controls = []

    def admits_only_after(name, mutant, rho):
        if satisfied(rows, rho) or not satisfied(mutant, rho):
            raise AssertionError(f'{name}: original rejection and weakened acceptance not both observed')
        controls.append(name)

    def remove_assertion(block):
        result = deepcopy(rows)
        del result[selected['blocks'][block][-1]['index']]
        return result

    admits_only_after('dummy amount may not be nonzero', remove_assertion('optional.amount'),
                      assignment(selected, dummy=1, amount=(7, 9)))
    admits_only_after('optional real root must equal anchor', remove_assertion('optional.anchor'),
                      assignment(selected, roots=(29, 31)))
    admits_only_after('required root must equal anchor', remove_assertion('required.anchor'),
                      assignment(selected, roots=(31, 29)))
    admits_only_after('required nullifier must equal real hash-output wire', remove_assertion('required.nullifier'),
                      assignment(selected, nullifiers=(33, 19)))
    admits_only_after('optional nullifier must equal selected hash-output wire', remove_assertion('optional.nullifier'),
                      assignment(selected, nullifiers=(17, 23)))
    rho = assignment(selected)
    history_column = selected['observations']['spend1.history']['linear'][0][0]
    rho[history_column] = 1
    admits_only_after('history must equal real-and-old', remove_assertion('optional.history'), rho)

    rho = assignment(selected)
    rho[selected['observations']['spend0.position']['linear'][0][0]] = 40
    admits_only_after('position must equal its reconstructed bits', remove_assertion('spend0.position'), rho)

    # Replace dummy with (1-dummy) in BOTH actual square rows of the nullifier
    # selector, keeping the original linking assertion. Bad output now passes.
    rho = assignment(selected, nullifiers=(17, 23))
    mutant = deepcopy(rows)
    gate = selected['gates']['optional.nullifier']
    dummy_column = selected['observations']['spend1.dummy']['linear'][0][0]
    for original in selected['blocks']['optional.nullifier'][:2]:
        row = mutant[original['index']]
        coefficients = {i: int(c, 16) for i, c in row['a']}
        coefficients[dummy_column] = (coefficients.get(dummy_column, 0) - 2) % P
        coefficients[selected['outline']] = (coefficients.get(selected['outline'], 0) + 1) % P
        row['a'] = [[i, f'{c:064x}'] for i, c in sorted(coefficients.items()) if c]
    x, y = 1 - rho[dummy_column], evaluate(gate['y'], rho)
    rho[gate['difference']] = (x - y) ** 2 % P
    rho[gate['output']] = x * y % P
    admits_only_after('nullifier selector polarity', mutant, rho)

    # A nonboolean high bit represents 2^48; the other input, difference and
    # shared floor still have legal ordinary bit decompositions.
    rho = assignment(selected, position=(2**48, 12), floor=1)
    high = selected['bits']['spend0.position'][-1]
    rho[high] = 2
    mutant = deepcopy(rows)
    del mutant[selected['blocks']['spend0.position'][-2]['index']]
    admits_only_after('position high bit must be boolean', mutant, rho)

    # Moving the strict-history boundary by one wrongly classifies equality as
    # old. This mutation changes the actual square-linear comparator row.
    rho = assignment(selected, position=(10, 10), floor=10, borrow=(0, 1))
    rho[selected['observations']['spend1.difference']['linear'][0][0]] = 2**48 - 1
    for bit in selected['bits']['spend1.difference']:
        rho[bit] = 1
    mutant = deepcopy(rows)
    row = mutant[selected['blocks']['spend1.comparison'][0]['index']]
    row['a'].append([selected['outline'], f'{P-1:064x}'])
    row['a'].sort()
    admits_only_after('floor equality is recent', mutant, rho)

    metadata = [
        ('required literal', lambda e: e['literals'][0].update(value=f'{1:064x}'), 'literal zero'),
        ('public anchor slot', lambda e: next(x for x in e['expressions'] if x['label'] == 'statement.2').update(
            source=next(x for x in e['expressions'] if x['label'] == 'statement.12')['source']), 'slot/source'),
    ]
    rejected = []
    for name, change, reason in metadata:
        mutant = deepcopy(export)
        change(mutant)
        try:
            select(mutant)
        except ValueError as error:
            if reason not in str(error):
                raise AssertionError(f'{name}: wrong rejection cause') from error
        else:
            raise AssertionError(f'{name}: bad metadata accepted')
        rejected.append(name)
    return {'scope': 'actual selected-row adversarial assignments; opaque hash-output wires',
            'positive_assignments': len(positives), 'semantic_counterexamples': controls,
            'preserving_tail_extensions': extensions,
            'source_mapping_rejections': rejected}
