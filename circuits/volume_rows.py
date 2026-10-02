"""Select exact arithmetic templates from actual Transfer compiler rows.

Selection and full-relation membership remain an explicit trusted exporter/checker
boundary. Generated Lean separately checks each selected field relation.
"""
from generate import P

BOUND = 2**128


def select(export):
    if export['subject'] != 'actual Transfer amount/volume arithmetic row subset':
        raise ValueError('wrong volume export subject')
    if export['scalar_encoding'] != 'canonical-big-endian-32' or int(export['modulus_minus_one'], 16) != P-1:
        raise ValueError('wrong volume scalar field')
    domain = export['domain_size']
    if type(domain) is not int or domain < 4 or domain & (domain - 1):
        raise ValueError('invalid domain size')
    variables, groups = export['variables'], export['bit_columns']
    if len(variables) != 7 or len(groups) != 6 or any(len(bits) != 128 for bits in groups):
        raise ValueError('wrong arithmetic observation shape')
    all_columns = variables + [column for group in groups for column in group]
    if len(set(all_columns)) != len(all_columns) or any(type(i) is not int or not 3 <= i < export['domain_size'] for i in all_columns):
        raise ValueError('aliased or invalid arithmetic column roles')

    def linear(terms):
        combined = {}
        for column, coefficient in terms:
            combined[column] = (combined.get(column, 0) + coefficient) % P
        return tuple((i, c if c <= P//2 else c-P) for i,c in sorted(combined.items()) if c)

    def parsed(terms):
        if any(type(i) is not int or not 0 <= i < domain for i, _ in terms):
            raise ValueError('invalid row column')
        actual = [(i, int(c,16)) for i,c in terms]
        if any(len(c) != 64 for _,c in terms) or any(not 0 < c < P for _,c in actual):
            raise ValueError('noncanonical coefficient')
        if any(actual[i][0] >= actual[i+1][0] for i in range(len(actual)-1)):
            raise ValueError('noncanonical columns')
        return linear(actual)

    table = {}
    original_indices = {}
    for row in export['rows']:
        index = row['index']
        if type(index) is not int or not 0 <= index < export['row_count']:
            raise ValueError('invalid original row index')
        key = (parsed(row['a']), parsed(row['b']))
        if index in original_indices and original_indices[index] != key:
            raise ValueError('contradictory original row index')
        original_indices[index] = key
        table.setdefault(key, row)

    def get(a,b=()):
        key = (linear(a), linear(b))
        if key not in table:
            raise ValueError(f'missing actual arithmetic row: {key}')
        return table[key]

    def weighted(bits, factor=1):
        return [(column, factor * 2**i) for i,column in enumerate(bits)]

    prior, successor, outbound, limit, real, borrow, difference = variables
    outbound_bits, prior_bits, successor_bits, candidate_bits, limit_bits, difference_bits = groups
    values = [[(outbound,1)],[(prior,1)],[(successor,1)],[(prior,1),(outbound,1)],[(limit,1)],[(difference,1)]]
    blocks = {}
    for name,bits,value in zip(['outbound','prior','successor','candidate','limit','difference'], groups, values):
        blocks[name] = [get([(column,1)],[(column,1)]) for column in bits]
        blocks[name].append(get(weighted(bits)+[(i,-c) for i,c in value]))
    blocks['comparison'] = [get(weighted(limit_bits)+weighted(candidate_bits,-1)+[(difference,-1),(borrow,BOUND)])]
    blocks['booleans'] = [get([(real,1)],[(real,1)]),get([(borrow,1)],[(borrow,1)])]

    def product_zero(name,x,y):
        minus = linear(x+[(i,-c) for i,c in y])
        candidates = [(b,row) for (a,b),row in table.items() if a == minus and len(b)==1 and b[0][1]==1]
        if len(candidates) != 1:
            raise ValueError(f'{name}: ambiguous or missing difference-square row')
        (difference_column,_), minus_row = candidates[0][0][0], candidates[0][1]
        plus = linear(x+y)
        matches = [(b,row) for (a,b),row in table.items() if a==plus and dict(b).get(difference_column)==1 and len(b)==2]
        if len(matches) != 1:
            raise ValueError(f'{name}: ambiguous or missing product row')
        b, plus_row = matches[0]
        output = [(i,c) for i,c in b if i!=difference_column]
        if len(output)!=1 or output[0][1]!=4:
            raise ValueError(f'{name}: wrong product scaling')
        output_column = output[0][0]
        if any(not 3 <= column < domain for column in (difference_column, output_column)):
            raise ValueError(f'{name}: invalid private product auxiliary')
        if difference_column in all_columns or output_column in all_columns or difference_column == output_column:
            raise ValueError(f'{name}: aliased product auxiliary')
        zero_rows = [table[key] for sign in (1,-1)
                     if (key := (linear([(output_column,sign)]), ())) in table]
        if len(zero_rows) != 1:
            raise ValueError(f'{name}: ambiguous or missing product-zero row')
        blocks[name] = [minus_row, plus_row, zero_rows[0]]
        return {'difference':difference_column,'output':output_column}

    gates = {
        'successor_gate': product_zero('successor_gate',[(real,1)],[(successor,1),(prior,-1),(outbound,-1)]),
        'limit_gate': product_zero('limit_gate',[(real,1)],[(borrow,1)]),
    }
    auxiliaries = [column for gate in gates.values() for column in gate.values()]
    if len(set(auxiliaries)) != 4:
        raise ValueError('aliased gate auxiliaries')
    return {'variables':variables,'bits':groups,'blocks':blocks,'gates':gates}
