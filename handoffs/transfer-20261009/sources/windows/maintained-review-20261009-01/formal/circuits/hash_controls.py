"""Arbitrary-assignment sensitivity controls for one actual Poseidon round.

The assignments satisfy only the explicitly selected round slice. In particular
zero-valued input point coordinates here are not claimed valid group witnesses
or satisfying assignments of the full Transfer relation.
"""
import hashlib
import json
from pathlib import Path
import sys

try:
    from .hash_rows import select
    from .poseidon_graph import P, decode_json
except ImportError:
    from hash_rows import select
    from poseidon_graph import P, decode_json


def check(export, parameter_root):
    selected = select(export, parameter_root)
    call = next(item for item in selected['calls'] if item['role'] == 'authorization.ivk')
    segment = next(item for item in call['segments']
                   if item['kind'] == 'round' and item['chunk'] == 0 and item['index'] == 0)
    indices = sorted(set(segment['rows']) | {selected['constant_link']})
    rows = {index: selected['rows'][index] for index in indices}
    fixed = {0, selected['outline']}
    occupied = set()

    def pivot(terms):
        if len(terms) != 1 or terms[0][1] != 1 or terms[0][0] < 3:
            raise ValueError('unsupported round control pivot')
        column = terms[0][0]
        if column in fixed or column in occupied:
            raise ValueError('aliased round control pivot')
        occupied.add(column)
        return column

    lanes = {}
    for lane, certificate in segment['fifths'].items():
        if certificate['kind'] == 'arithmetic':
            lanes[lane] = tuple(pivot(terms) for terms in (
                certificate['square'], certificate['fourth'], segment['transformed'][lane],
                certificate['auxiliary']))
    if not lanes:
        raise ValueError('round control needs actual arithmetic rows')
    boundary_support = {column for state in ('before', 'shifted')
                        for terms in segment[state] for column, _ in terms}
    boundary_support.update(column for lane, terms in enumerate(segment['transformed'])
                            if lane not in lanes for column, _ in terms)
    if occupied & boundary_support:
        raise ValueError('round control overwrites shared input boundary')

    def evaluate(terms, rho):
        return sum(coefficient * rho.get(column, 0) for column, coefficient in terms) % P

    def violated(rho, omitted=None):
        return [index for index, (left, right) in rows.items() if index != omitted
                and evaluate(left, rho) ** 2 % P != evaluate(right, rho)]

    def independent_round(rho):
        params = call['parameters']
        # This selected round is a full nonlinear round. The implementation
        # below evaluates the independent ARK/x^5/MDS equation directly.
        before = [evaluate(terms, rho) for terms in segment['before']]
        transformed = [pow(value + coefficient, 5, P)
                       for value, coefficient in zip(before, params['ark'][0])]
        return [sum(coefficient * value for coefficient, value in zip(row, transformed)) % P
                for row in params['mds']]

    def after(rho):
        return [evaluate(terms, rho) for terms in segment['after']]

    honest = {0: 1, selected['outline']: 1}
    for lane, (square, fourth, output, auxiliary) in lanes.items():
        base = evaluate(segment['shifted'][lane], honest)
        honest[square] = base * base % P
        honest[fourth] = honest[square] ** 2 % P
        honest[output] = honest[fourth] * base % P
        honest[auxiliary] = (honest[fourth] - base) ** 2 % P
    expected = independent_round(honest)
    if violated(honest) or after(honest) != expected:
        raise ValueError('original round control assignment does not satisfy the actual rows/specification')

    lane = min(lanes)
    square, fourth, output, auxiliary = lanes[lane]
    certificate = segment['fifths'][lane]
    base = evaluate(segment['shifted'][lane], honest)
    controls = []
    for position, name in enumerate(('square', 'fourth', 'product-minus', 'product-plus')):
        rho = dict(honest)
        if position == 0:
            rho[square] = (rho[square] + 1) % P
            rho[fourth] = rho[square] ** 2 % P
            rho[output] = rho[fourth] * base % P
            rho[auxiliary] = (rho[fourth] - base) ** 2 % P
        elif position == 1:
            rho[fourth] = (rho[fourth] + 1) % P
            rho[output] = rho[fourth] * base % P
            rho[auxiliary] = (rho[fourth] - base) ** 2 % P
        elif position == 2:
            rho[output] = (rho[output] + 1) % P
            rho[auxiliary] = ((rho[fourth] + base) ** 2 - 4 * rho[output]) % P
        else:
            rho[output] = (rho[output] + 1) % P
        omitted = certificate['rows'][position]
        if (violated(rho) != [omitted] or violated(rho, omitted)
                or independent_round(rho) != expected or after(rho) == expected):
            raise ValueError(f'{name} mutation did not exhibit the intended round semantic failure')
        controls.append({'removed_original_row': omitted, 'role': name,
                         'assignment_default': 0, 'assignment': sorted(rho.items()),
                         'original_rejects_only_removed_row': True,
                         'weakened_slice_accepts': True, 'independent_round_output_differs': True})
    key_indices = sorted({selected['constant_link']} | {link['row'] for link in selected['authorization_links']})
    key_rows = {index: selected['rows'][index] for index in key_indices}
    key_columns = set()
    for link in selected['authorization_links']:
        for role in ('computed', 'statement'):
            terms = link[role]
            if (len(terms) != 1 or terms[0][1] != 1 or terms[0][0] < 3
                    or terms[0][0] in fixed or terms[0][0] in key_columns):
                raise ValueError('unsupported/aliased key-link control pivot')
            key_columns.add(terms[0][0])
    key_controls = []
    for link in selected['authorization_links']:
        rho = {0: 1, selected['outline']: 1, link['computed'][0][0]: 1}
        failures = [index for index, (left, right) in key_rows.items()
                    if evaluate(left, rho) ** 2 % P != evaluate(right, rho)]
        if failures != [link['row']] or evaluate(link['computed'], rho) == evaluate(link['statement'], rho):
            raise ValueError('missing key equality row did not permit the intended coordinate mismatch')
        key_controls.append({'axis': link['axis'], 'removed_original_row': link['row'],
                             'assignment_default': 0, 'assignment': sorted(rho.items()),
                             'original_rejects_only_removed_row': True, 'weakened_slice_accepts': True,
                             'computed_and_statement_coordinate_differ': True})
    scope = ('actual IVK chunk0 round0 and separate action-key wire slices only; not full relation satisfiability'
             if key_controls else 'actual IVK chunk0 round0 only; not full relation satisfiability')
    return {'scope': scope,
            'rows': indices, 'one_positive': True, 'round_semantic_controls': controls,
            'original_expected_round_output': expected,
            'key_link_rows': key_indices if key_controls else [], 'key_link_controls': key_controls}


def summary(receipt):
    return {'positive':int(receipt['one_positive']),
            'round_semantic_controls':len(receipt['round_semantic_controls']),
            'key_link_controls':len(receipt['key_link_controls']), 'scope':receipt['scope']}


if __name__ == '__main__':
    source, runtime, destination = map(Path, sys.argv[1:])
    raw = source.read_bytes()
    receipt = check(decode_json(raw.decode()), runtime / 'crates/crypto/primitives/params')
    receipt['export_sha256'] = hashlib.sha256(raw).hexdigest()
    receipt['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    destination.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(summary(receipt)))
