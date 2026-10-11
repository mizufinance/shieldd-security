"""Independently read literal Lean lookup trees; do not execute producer generator."""
import hashlib
import json
import re
from pathlib import Path

J = Path(__file__).resolve().parent
S = J.parent.parent / 'mac-arithmetic-coefficients39-source01'
sources = S / 'source-root/ShielddSecurity'
data = S / 'coefficients01.json'
cs = json.loads(data.read_bytes())['coefficients']
assert len(cs) == 7483 and cs == sorted(set(cs))

def parse(expression, outer=False):
    pattern = r'ArithmeticCoefficients39C\d{2}\.value|\d+|[()]|<|\b(?:if|index|then|else)\b'
    matches = list(re.finditer(pattern, expression))
    position = 0
    for match in matches:
        assert not expression[position:match.start()].strip()
        position = match.end()
    assert not expression[position:].strip()
    tokens = [m.group(0) for m in matches]
    cursor = 0

    def consume(value=None):
        nonlocal cursor
        assert cursor < len(tokens)
        token = tokens[cursor]
        cursor += 1
        assert value is None or token == value
        return token

    def node():
        token = consume()
        if token == '(':
            consume('if')
            consume('index')
            consume('<')
            cut = int(consume())
            consume('then')
            left = node()
            consume('else')
            right = node()
            consume(')')
            return (cut, left, right)
        if outer:
            assert re.fullmatch(r'ArithmeticCoefficients39C\d{2}\.value', token)
            consume('index')
            return token.removesuffix('.value')
        assert token.isdigit()
        return int(token)

    tree = node()
    assert cursor == len(tokens)
    return tree

def lookup(tree, index):
    while isinstance(tree, tuple):
        cut, left, right = tree
        tree = left if index < cut else right
    return tree

leaves = {}
identities = []
for part in range(8):
    name = f'ArithmeticCoefficients39C{part:02d}'
    path = sources / (name + '.lean')
    text = path.read_text()
    match = re.search(r'^def value \(index : Nat\) : Int := if (\d+)≤index ∧ index<(\d+) then (.*) else 0$', text, re.M)
    assert match
    low, high = int(match[1]), int(match[2])
    assert (low, high) == (part * 1024, min((part + 1) * 1024, len(cs)))
    tree = parse(match[3])
    assert [lookup(tree, i) for i in range(low, high)] == cs[low:high]
    leaves[name] = (low, high, tree)
    identities.append({'module': name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                       'low': low, 'high': high})

outer_path = sources / 'ArithmeticCoefficients39.lean'
match = re.search(r'^def value \(index : Nat\) : Int := (.*)$', outer_path.read_text(), re.M)
assert match
tree = parse(match[1], outer=True)
for index in range(8193):
    low, high, body = leaves[lookup(tree, index)]
    actual = lookup(body, index) if low <= index < high else 0
    expected = cs[index] if index < len(cs) else 0
    assert actual == expected
result = {
    'kind': 'Independent lexical lookup-tree interpretation; source/data evidence only',
    'coefficient_store_sha256': hashlib.sha256(data.read_bytes()).hexdigest(),
    'coefficients_checked': len(cs), 'outer_dispatch_indices_checked': 8193,
    'leaf_sources': identities,
    'outer_source_sha256': hashlib.sha256(outer_path.read_bytes()).hexdigest(),
    'outside_behavior': 'Each leaf has explicit bounds and returns0 outside; outer dispatch selects final leaf above7168',
    'kernel_replay': False, 'full_transfer': 'OPEN'
}
(J / 'coefficient-dispatch-review01.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'leaf_sources'}))
