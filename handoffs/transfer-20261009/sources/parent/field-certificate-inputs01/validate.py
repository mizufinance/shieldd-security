"""Independent data validation of candidate Lucas certificates; no Lean credit."""
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path

MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def validate(data):
    require(data['modulus'] == MODULUS, 'wrong pinned modulus')
    entries = data['certificates']
    seen = set()
    active = set()

    def visit(n):
        require(type(n) is int and n >= 2, 'invalid candidate integer')
        require(n not in active, 'certificate dependency cycle')
        if n in seen:
            return
        key = str(n)
        require(key in entries, 'missing dependency certificate')
        item = entries[key]
        require(item['n'] == n, 'certificate key mismatch')
        fs = item['factors']
        require(isinstance(fs, list), 'factor list missing')
        if n == 2:
            require(item == {'n': 2, 'base': 1, 'factors': [], 'residues': []},
                    'invalid base certificate')
            seen.add(n)
            return
        require(fs and all(type(q) is int and 2 <= q < n for q in fs),
                'invalid factor range')
        require(math.prod(fs) == n - 1, 'incomplete factorization')
        active.add(n)
        for q in fs:
            visit(q)
        active.remove(n)
        base = item['base']
        require(type(base) is int and 1 < base < n, 'invalid Lucas base')
        require(pow(base, n - 1, n) == 1, 'full-power identity failed')
        expected = []
        for q in sorted(set(fs)):
            exponent = (n - 1) // q
            residue = pow(base, exponent, n)
            require(residue != 1, 'proper-factor power equals one')
            expected.append({'q': q, 'exponent': exponent, 'residue': residue})
        require(item['residues'] == expected, 'wrong or missing power residue')
        seen.add(n)

    visit(MODULUS)
    require(set(entries) == {str(n) for n in seen}, 'unused certificate entry')
    require(data['factorization'] == entries[str(MODULUS)]['factors'],
            'root factorization mismatch')
    d, i = data['coefficient_d'], data['imaginary']
    require(type(d) is int and 0 <= d < MODULUS, 'noncanonical d')
    require(type(i) is int and 0 <= i < MODULUS, 'noncanonical imaginary')
    require(10241 * d + 10240 == data['coefficient_d_equation_quotient'] * MODULUS,
            'coefficient equation failed')
    require(i * i + 1 == data['imaginary_square_quotient'] * MODULUS,
            'imaginary equation failed')
    require(data['nonsquare_exponent'] == (MODULUS - 1) // 2,
            'wrong nonsquare exponent')
    require(data['nonsquare_residue'] == MODULUS - 1 ==
            pow(d, data['nonsquare_exponent'], MODULUS), 'nonsquare residue failed')
    return len(seen)


def controls(original):
    mutations = {
        'wrong_modulus': lambda d: d.update(modulus=MODULUS - 2),
        'missing_dependency': lambda d: d['certificates'].pop('2'),
        'missing_factor': lambda d: d['certificates'][str(MODULUS)]['factors'].pop(),
        'wrong_residue': lambda d: d['certificates'][str(MODULUS)]['residues'][0].update(residue=1),
        'unit_base': lambda d: d['certificates'][str(MODULUS)].update(base=1),
        'wrong_imaginary': lambda d: d.update(imaginary=d['imaginary'] + 1),
        'wrong_coefficient': lambda d: d.update(coefficient_d=d['coefficient_d'] + 1),
        'wrong_exponent': lambda d: d.update(nonsquare_exponent=1),
    }
    results = []
    for name, change in mutations.items():
        data = copy.deepcopy(original)
        change(data)
        try:
            validate(data)
        except ValueError as exc:
            results.append({'control': name, 'outcome': 'rejected', 'reason': str(exc)})
        else:
            raise ValueError('control unexpectedly accepted: ' + name)
    return results


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    raw = args.candidate.read_bytes()
    data = json.loads(raw)
    report = {
        'kind': 'Python data validation only; no kernel or field-instance credit',
        'candidate_sha256': hashlib.sha256(raw).hexdigest(),
        'certificate_count': validate(data),
    }
    if args.controls:
        report['controls'] = controls(data)
    print(json.dumps(report, indent=2))
