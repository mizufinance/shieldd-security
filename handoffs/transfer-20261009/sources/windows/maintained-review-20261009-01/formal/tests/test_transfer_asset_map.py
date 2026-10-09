"""Typed map cone, complete streaming fixtures and semantic row refusals."""
import copy
import io
import json
import unittest

from blake3 import blake3
from circuits import transfer_asset_map as asset_map, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine

P = relation.MODULUS


def encoded(value):
    return (json.dumps(value, separators=(',', ':')) + '\n').encode()


def square_root(n):
    """Finite Tonelli-Shanks fixture arithmetic, independent of map witnesses."""
    n %= P
    if not n:
        return 0
    if pow(n, (P - 1) // 2, P) != 1:
        return None
    q, s = P - 1, 0
    while not q & 1:
        q //= 2
        s += 1
    z = 2
    while pow(z, (P - 1) // 2, P) != P - 1:
        z += 1
    c, t, root, m = pow(z, q, P), pow(n, q, P), pow(n, (q + 1) // 2, P), s
    for _ in range(s):
        if t == 1:
            return root
        i, cur = 0, t
        while cur != 1 and i < m:
            cur = cur * cur % P
            i += 1
        if i == m:
            raise AssertionError('fixture square-root recurrence failed')
        b = pow(c, 1 << (m - i - 1), P)
        root = root * b % P
        c = b * b % P
        t = t * c % P
        m = i
    raise AssertionError('fixture finite square-root budget')


class Builder:
    """Shared field equations, with each product's actual auxiliary retained."""
    def __init__(self):
        self.expressions = {}
        self.nodes = []
        self.rows = []
        self.rho = {0: 1, 32000: 1}
        self.next_witness, self.next_column = 0, 5000
        self.constants = {}

    def lc(self, ref):
        return self.expressions[tuple(ref['source'])]

    def val(self, ref):
        return sum(v * self.rho.get(c, 0) for c, v in self.lc(ref)) % P

    def constant(self, n):
        n %= P
        if n not in self.constants:
            self.constants[n] = [0, len(self.constants)]
            self.expressions[tuple(self.constants[n])] = canonical([(0, n)])
        return {'source': self.constants[n]}

    def witness(self, n, boolean=False):
        h = (1, self.next_witness)
        self.next_witness += 1
        self.expressions[h] = ((3 + h[1], 1),)
        self.rho[3 + h[1]] = n % P
        ref = {'source': list(h)}
        if boolean:
            self.rows.append((self.lc(ref), self.lc(ref)))
        return ref

    def binary(self, a, b, multiply):
        aa, bb = self.lc(a), self.lc(b)
        constant = lambda v: not v or len(v) == 1 and v[0][0] == 0
        if constant(aa) and constant(bb):
            return self.constant(self.val(a) * self.val(b) if multiply else self.val(a) + self.val(b))
        if constant(bb):
            a, b = b, a
            aa, bb = bb, aa
        i = len(self.nodes)
        self.nodes.append(dict(index=i, multiply=multiply, left=a['source'], right=b['source']))
        out = {'source': [2, i]}
        if not multiply:
            lc = combine(aa, bb)
        elif constant(aa):
            lc = canonical((c, v * self.val(a)) for c, v in bb)
        else:
            col = self.next_column
            self.next_column += 1
            lc = ((col, 1),)
            self.rho[col] = self.val(a) * self.val(b) % P
            if aa == bb:
                self.rows.append((aa, lc))
            else:
                aux_col = self.next_column
                self.next_column += 1
                auxiliary = ((aux_col, 1),)
                self.rho[aux_col] = (self.val(a) - self.val(b))**2 % P
                self.rows.extend([(combine(aa, bb, -1), auxiliary),
                                  (combine(aa, bb), combine(auxiliary, lc, 4))])
        self.expressions[2, i] = lc
        return out

    def add(self, a, b):
        return self.binary(a, b, False)

    def mul(self, a, b):
        return self.binary(a, b, True)

    def neg(self, a):
        return self.mul(self.constant(-1), a)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def assertion(self, a, b):
        lc = combine(self.lc(a), self.lc(b), -1)
        if lc:
            self.rows.append((lc, ()))

    def inverse(self, a):
        inv = self.witness(pow(self.val(a), -1, P))
        self.assertion(self.mul(inv, a), self.constant(1))
        return inv

    def select(self, bit, yes, no):
        return self.add(no, self.mul(bit, self.sub(yes, no)))


def fixture(u=0,*,hash_builder=None):
    b = Builder()
    asset = b.witness(17)
    hash_ref = b.witness(u) if hash_builder is None else hash_builder(b,asset)
    c1, c2 = b.constant(asset_map.C1), b.constant(asset_map.C2)
    k, one, zero_const = b.constant(asset_map.K), b.constant(1), b.constant(0)
    tv = b.mul(b.mul(b.constant(5), hash_ref), hash_ref)
    den1 = b.add(one, tv)
    inv1 = b.inverse(den1)
    x1 = b.mul(b.neg(c1), inv1)
    gx1 = b.mul(b.add(b.mul(b.add(x1, c1), x1), c2), x1)
    x2 = b.sub(b.neg(x1), c1)
    gx2 = b.mul(tv, gx1)
    square = b.witness(int(square_root(b.val(gx1)) is not None), True)
    qr_root = b.witness(square_root(b.val(gx1) if b.val(square) else 5 * b.val(gx1)))
    qr = [b.mul(qr_root, qr_root), b.select(square, gx1, b.mul(b.constant(5), gx1))]
    b.assertion(*qr)
    x, y_squared = b.select(square, x1, x2), b.select(square, gx1, gx2)
    yn = square_root(b.val(y_squared))
    if (yn & 1) != b.val(square):
        yn = -yn % P
    y = b.witness(yn)
    y_square = b.mul(y, y)
    b.assertion(y_square, y_squared)
    bits = [b.witness((yn >> i) & 1, True) for i in range(255)]
    total = zero_const
    for i, bit in enumerate(bits):
        total = b.add(total, b.mul(bit, b.constant(2**i)))
    b.assertion(total, y)
    le = one
    for i, bit in enumerate(bits):
        other = b.constant(((P - 1) >> i) & 1)
        inverse_bit = b.sub(one, bit)
        both = b.mul(inverse_bit, other)
        unequal = b.sub(b.add(inverse_bit, other), b.add(both, both))
        le = b.add(both, b.mul(le, unequal))
    b.rows.append((b.lc(le), b.lc(le)))
    b.assertion(le, one)
    b.assertion(bits[0], square)
    s, t = b.mul(x, k), b.mul(y, k)
    plus = b.add(s, one)
    denominator = b.mul(plus, t)
    is_zero = b.witness(int(b.val(denominator) == 0), True)
    inverse = b.witness(pow(b.val(denominator), -1, P) if b.val(denominator) else 0)
    products = [y_square, b.mul(denominator, inverse), b.mul(denominator, is_zero), b.mul(inverse, is_zero)]
    b.assertion(products[1], b.sub(one, is_zero))
    b.assertion(products[2], zero_const)
    b.assertion(products[3], zero_const)
    point = [b.mul(b.mul(inverse, plus), s),
             b.add(b.mul(b.mul(inverse, t), b.sub(s, one)), is_zero)]
    points, aux = [point], []
    for _ in range(3):
        xx, yy = b.mul(point[0], point[0]), b.mul(point[1], point[1])
        dt = b.mul(b.mul(xx, yy), b.constant(asset_map.D))
        plus_d, minus_d = b.add(one, dt), b.sub(one, dt)
        divisor = b.mul(plus_d, minus_d)
        inv_d = b.inverse(divisor)
        point = [b.mul(b.mul(b.add(b.mul(point[0], point[1]), b.mul(point[1], point[0])), minus_d), inv_d),
                 b.mul(b.mul(b.add(yy, xx), plus_d), inv_d)]
        aux.append([xx, yy, dt, plus_d, minus_d, divisor, inv_d])
        points.append(point)
    values = [hash_ref, tv, den1, inv1, x1, gx1, x2, gx2, square, qr_root, x,
              y_squared, y, s, t, plus, denominator, is_zero, inverse]
    roles = [asset, hash_ref, *values, *qr, total, le, *products,
             *(r for point in points for r in point), *(r for a in aux for r in a), *bits]
    required = {tuple(ref['source']) for ref in roles}
    pending = list(required)
    nodes = set()
    while pending:
        h = pending.pop()
        if h in {tuple(asset['source']), tuple(hash_ref['source'])} or h[0] != 2 or h[1] in nodes:
            continue
        nodes.add(h[1])
        node = b.nodes[h[1]]
        for key in ('left', 'right'):
            child = tuple(node[key])
            required.add(child)
            pending.append(child)
    copy_column, domain = 32000, 32768
    outline = lambda lc: canonical((copy_column if c == 0 else c, n) for c, n in lc)
    rows = [(canonical([(0, 1), (copy_column, -1)]), ())] + [(outline(a), outline(c)) for a, c in b.rows]
    records = [dict(row=i, a=[[c, f'{n:064x}'] for c, n in a], b=[[c, f'{n:064x}'] for c, n in bb])
               for i, (a, bb) in enumerate(rows)]
    public, block = [[1, 990]], [[1, 991]]
    digest = blake3()
    digest.update(relation.NAMESPACE + relation.u64(domain) + relation.u64(len(rows)) +
                  relation.indices(public) + relation.u64(1) + relation.indices(block))
    for row in records:
        digest.update(b'A' + relation.terms(row['a'], domain) + b'B' + relation.terms(row['b'], domain))
    identity = dict(relation_digest=digest.hexdigest(), domain_size=domain, full_rows=len(rows), constant_copy=copy_column)
    obj = dict(schema='shieldd-transfer-asset-map-v1', family='transfer', scope=asset_map.SCOPE, **identity,
               ordinary_full_ordered_rows_equal=True, repeated_observations_equal=True, asset=asset, hash=hash_ref,
               values=values, y_bits=[ref['source'] for ref in bits], cofactor=points, cofactor_aux=aux,
               constraint_products=products, qr=qr, canonical=[total, le],
               expressions=[dict(source=list(h), terms=[[c, f'{n:064x}'] for c, n in b.expressions[h]]) for h in sorted(required)],
               nodes=[b.nodes[i] for i in sorted(nodes)])
    caller = dict(metadata=dict(**identity, caller=dict(asset=asset)), observed={tuple(asset['source']): b.lc(asset)})
    header = dict(schema='shieldd-transfer-relation-v1', family='transfer', relation_digest=identity['relation_digest'],
                  domain_size=domain, stored_rows=len(rows), public_inputs=1, committed_blocks=[1], constant_column=0,
                  public_columns=[1], committed_columns=[[2]], source_public=public, source_blocks=[block],
                  coefficient_encoding='canonical-big-endian-32', field_modulus=str(P),
                  role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
                  padding='implicit-all-zero-rows-to-domain-size')
    stream = io.BytesIO(b''.join(encoded(v) for v in [header, *records, dict(eof=True, rows=len(rows))]))
    return encoded(obj), caller, stream, rows, b


class AssetMapTests(unittest.TestCase):
    def test_sparse_affine_cone_has_identical_physical_products_and_strict_roots(self):
        data,caller,_,_,_=fixture(17)
        obj=json.loads(data);dense=asset_map.inspect_metadata(data,caller)
        selected={tuple(e['source']) for e in obj['expressions'] if e['source'][0]!=2}
        def roles(v):
            if isinstance(v,dict):
                if set(v)=={'source'}:selected.add(tuple(v['source']))
                else:
                    for child in v.values():roles(child)
            elif isinstance(v,list):
                for child in v:roles(child)
        roles({k:v for k,v in obj.items() if k not in ('expressions','nodes')})
        for node in obj['nodes']:
            if node['multiply'] and node['left'][0]!=0 and node['right'][0]!=0:
                selected.update(((2,node['index']),tuple(node['left']),tuple(node['right'])))
        sparse=copy.deepcopy(obj);sparse['expressions']=[e for e in obj['expressions'] if tuple(e['source']) in selected]
        checked=asset_map.inspect_metadata(encoded(sparse),caller)
        self.assertLess(len(sparse['expressions']),len(obj['expressions']))
        for key in ('observed','nonlinear','comparisons','points','canonical'):
            self.assertEqual(checked[key],dense[key])
        missing=copy.deepcopy(sparse)
        index=checked['nonlinear'][0][0]
        missing['expressions']=[e for e in missing['expressions'] if e['source']!=[2,index]]
        with self.assertRaises(relation.RelationError):asset_map.inspect_metadata(encoded(missing),caller)
        missing=copy.deepcopy(sparse);missing['nodes']=missing['nodes'][:-1]
        with self.assertRaises(relation.RelationError):asset_map.inspect_metadata(encoded(missing),caller)
        altered=copy.deepcopy(obj)
        affine=next(n for n in obj['nodes'] if not n['multiply'])
        lc=next(e for e in altered['expressions'] if e['source']==[2,affine['index']])
        lc['terms']=[[3,f'{1:064x}']]
        with self.assertRaises(relation.RelationError):asset_map.inspect_metadata(encoded(altered),caller)

    def test_generated_row_implications_are_bounded_and_audited(self):
        data, caller, stream, _, _ = fixture(17)
        extracted = asset_map.extract(data, stream, caller)
        modules = asset_map.generate_row_modules(data, extracted, caller, chunk_size=8)
        self.assertGreater(len(modules), 30)
        self.assertIn('RuntimeTransferAssetMapInverses', modules)
        wide = [name for name, source in modules.items() if 'set_option maxRecDepth 4096' in source]
        self.assertEqual(len(wide), 1)
        self.assertTrue(wide[0].startswith('RuntimeTransferAssetMapConstraints'))
        for name, source in modules.items():
            self.assertIn('set_option maxHeartbeats 500000', source)
            self.assertEqual(source.count('#print axioms'), source.count('#check @'))
            self.assertNotIn('native_decide', source)
            self.assertNotIn('sorry', source)
            self.assertNotIn('admit', source)
            self.assertNotIn('set_option maxHeartbeats 0', source)
            self.assertIn('(satisfied : Satisfies rho rawRows)', source)
            self.assertLess(source.count('theorem '), 10)
        for invalid in (True, 0, 33):
            with self.assertRaises(relation.RelationError):
                asset_map.generate_row_modules(data, extracted, caller, chunk_size=invalid)

    def test_comparator_fragments_keep_all255_bits_and_real_adjacency(self):
        data, caller, stream, _, _ = fixture(17)
        extracted = asset_map.extract(data, stream, caller)
        modules = asset_map.generate_comparison_modules(data, extracted, caller)
        self.assertEqual(len(modules), 32)
        self.assertEqual(sum(source.count('before :=') for source in modules.values()), 255)
        for source in modules.values():
            self.assertEqual(source.count('#check @'), 5)
            self.assertEqual(source.count('#print axioms'), 5)
            self.assertIn('ScalarIndexed.checked_chain_membership', source)
            self.assertIn('eval rho initial', source)
            self.assertNotIn('canonical_bound', source)
            self.assertLess(len(source), 8000)
        for invalid in (True, 0, 17):
            with self.assertRaises(relation.RelationError):
                asset_map.generate_comparison_modules(data, extracted, caller, chunk_size=invalid)

    def test_complete_encoding_composes_every_fragment_and_actual_boundaries(self):
        data, caller, stream, _, _ = fixture(17)
        extracted = asset_map.extract(data, stream, caller)
        source = asset_map.generate_encoding_module(data, extracted, caller)
        self.assertEqual(source.count('theorem included'), 32)
        self.assertEqual(source.count('theorem chain'), 32)
        self.assertEqual(source.count('theorem bits'), 32)
        self.assertEqual(source.count('theorem endpoint'), 32)
        self.assertEqual(source.count('import ShielddSecurity.RuntimeTransferAssetMapComparison'), 32)
        self.assertIn('FieldEncoding.checked_encoding', source)
        self.assertIn('ScalarChainComposition.chain_append', source)
        self.assertIn('theorem actual_parity', source)
        self.assertEqual(source.count('#check @'), source.count('#print axioms'))
        self.assertNotIn('native_decide', source)
        self.assertNotIn('canonicalBound', source)
        self.assertNotIn('steps.head!', source)
        # The right-associated suffixes only reference already-defined suffixes.
        self.assertLess(source.index('def suffix31'), source.index('def suffix30'))
        self.assertLess(source.index('def suffix1 :'), source.index('def suffix0 :'))
        changed = copy.deepcopy(extracted)
        changed['selected_rows'] = changed['selected_rows'][:-1]
        with self.assertRaises(relation.RelationError):
            asset_map.generate_encoding_module(data, changed, caller)

    def test_source_equations_and_all_original_row_templates(self):
        for u in (0, 1, 17, P - 1):
            data, caller, stream, rows, b = fixture(u)
            selected = asset_map.extract(data, stream, caller)
            checked = asset_map.certificates(data, selected, caller)
            self.assertEqual(len(checked['quotients']), 4)
            self.assertEqual(len(checked['checked']['comparisons']), 255)
            evaluate = lambda lc: sum(b.rho.get(c, 0) * n for c, n in lc) % P
            self.assertTrue(all(evaluate(a)**2 % P == evaluate(bb) for a, bb in rows))
            x, y = (b.val(ref) for ref in json.loads(data)['cofactor'][-1])
            self.assertEqual((y*y - x*x - 1 - asset_map.D*x*x*y*y) % P, 0)
            # A changed materialized product is a semantic failure on the exact
            # selected rows, not a compiler or resource failure.
            certificate = next(c for c in checked['nonlinear'] if c['kind'] == 'product')
            _, left, right, output = next(entry for entry in checked['checked']['nonlinear']
                                          if entry[0] == certificate['node'])
            self.assertEqual(len(output), 1)
            pivot = output[0][0]
            self.assertEqual(evaluate(output), evaluate(left) * evaluate(right) % P)
            b.rho[pivot] = (b.rho[pivot] + 1) % P
            self.assertNotEqual(evaluate(output), evaluate(left) * evaluate(right) % P)
            self.assertFalse(all(evaluate(a)**2 % P == evaluate(bb) for a, bb in checked['rows'].values()))

    def test_pending_roles_alias_topology_and_lc_drift_refuse(self):
        data, caller, _, _, _ = fixture()
        original = json.loads(data)
        changes = []
        pending = copy.deepcopy(original); pending['repeated_observations_equal'] = False; changes.append(pending)
        pending = copy.deepcopy(original); pending['ordinary_full_ordered_rows_equal'] = 1; changes.append(pending)
        alias = copy.deepcopy(original); alias['values'][9] = alias['values'][12]; changes.append(alias)
        bits = copy.deepcopy(original); bits['y_bits'][254] = bits['y_bits'][0]; changes.append(bits)
        node = copy.deepcopy(original); node['nodes'][-1]['left'] = [2, node['nodes'][-1]['index']]; changes.append(node)
        node = copy.deepcopy(original); node['nodes'][-1]['multiply'] = 1; changes.append(node)
        role = copy.deepcopy(original); role['cofactor'][3] = role['cofactor'][2]; changes.append(role)
        role = copy.deepcopy(original); role['canonical'][1] = role['values'][8]; changes.append(role)
        lc = copy.deepcopy(original)
        target = next(e for e in lc['expressions'] if e['source'] == lc['values'][13]['source'])
        target['terms'][0][1] = f'{(int(target["terms"][0][1],16) + 1) % P:064x}'
        changes.append(lc)
        for changed in changes:
            with self.assertRaises(relation.RelationError):
                asset_map.inspect_metadata(encoded(changed), caller)

    def test_persisted_rows_and_whole_stream_digest_are_not_interchangeable(self):
        data, caller, stream, _, _ = fixture(19)
        selected = asset_map.extract(data, stream, caller)
        changed = copy.deepcopy(selected)
        row = next(r for r in changed['selected_rows'] if r['row'] != 0 and r['b'])
        row['b'][0][1] = f'{(int(row["b"][0][1],16) + 1) % P:064x}'
        with self.assertRaises(relation.RelationError):
            asset_map.certificates(data, changed, caller)
        stream.seek(0)
        full = stream.getvalue().splitlines(keepends=True)
        row = json.loads(full[-2]); row['a'][0][1] = f'{(int(row["a"][0][1],16)+1)%P:064x}'
        full[-2] = encoded(row)
        with self.assertRaises(relation.RelationError):
            asset_map.extract(data, io.BytesIO(b''.join(full)), caller)


if __name__ == '__main__':
    unittest.main()
