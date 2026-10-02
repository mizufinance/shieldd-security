"""Semantic fault controls over arbitrary assignments to exported square rows."""
from copy import deepcopy
from generate import P, generate

if not __debug__:
    raise RuntimeError('semantic controls require Python assertions enabled')


def satisfies(export, assignment):
    def linear(terms):
        return sum(int(coefficient, 16) * assignment.get(column, 0) for column, coefficient in terms) % P
    return all(pow(linear(row['a']), 2, P) == linear(row['b']) for row in export['rows'])


def controls(export):
    generate(export)
    results = []
    # The highest bit can be 2 after its Boolean constraint is removed.
    # Reconstruction and public/committed/constant copies still hold, yet the
    # public input is 2^128, outside the proved range. These are arbitrary field
    # assignments, not values obtainable from honest Rust witness generation.
    bit = export['bit_columns'][-1]
    outline = max(export['value_column'], export['commitment_column'], *export['bit_columns']) + 1
    assignment = {0: 1, 1: 2**128, export['value_column']: 2**128, bit: 2, outline: 1}
    mutant = deepcopy(export)
    removed = mutant['rows'].pop(127)
    assert removed['a'][0][0] == bit and removed['b'][0][0] == bit
    assert not satisfies(export, assignment), 'original relation accepted the bad range assignment'
    assert satisfies(mutant, assignment), 'Boolean mutant did not admit the intended bad assignment'
    results.append('removed Boolean row admits public value 2^128')

    assignment = {0: 1, 1: 2**128, export['value_column']: 2**128, outline: 1}
    mutant = deepcopy(export)
    mutant['rows'].pop(128)
    assert not satisfies(export, assignment) and satisfies(mutant, assignment)
    results.append('removed reconstruction admits public value 2^128')

    assignment = {0: 1, 1: 2**128, outline: 1}
    mutant = deepcopy(export)
    mutant['rows'].pop(129)
    assert not satisfies(export, assignment) and satisfies(mutant, assignment)
    results.append('removed public copy admits a different out-of-range public input')

    mutant = deepcopy(export)
    mutant['commitment_column'] = mutant['value_column']
    mutant['rows'][130]['a'][1][0] = mutant['value_column']
    try:
        generate(mutant)
    except ValueError as error:
        assert 'altered complete range column roles' in str(error)
    else:
        raise AssertionError('aliased commitment/value roles escaped checker')
    results.append('aliased commitment/value roles: expected semantic checker rejection')

    # Structural controls reject the intended unsupported semantic identity;
    # exceptions unrelated to the exact error are never accepted as detection.
    for label, mutate, message in [
        ('constant link', lambda x: x['rows'].pop(), 'altered complete range'),
        ('column map', lambda x: x.__setitem__('value_column', x['value_column'] + 1), 'altered complete range'),
        ('field', lambda x: x.__setitem__('modulus_minus_one', '00' * 32), 'unsupported scalar'),
        ('layout', lambda x: x.__setitem__('public_inputs', 2), 'unsupported layout'),
    ]:
        mutant = deepcopy(export)
        mutate(mutant)
        try:
            generate(mutant)
        except ValueError as error:
            assert message in str(error), (label, error)
        else:
            raise AssertionError(f'{label} mutation escaped row checker')
        results.append(f'{label}: expected semantic checker rejection')
    return results
