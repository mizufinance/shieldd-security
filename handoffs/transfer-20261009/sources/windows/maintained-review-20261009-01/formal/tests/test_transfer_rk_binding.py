"""Synthetic digest-framed RK equality controls; no real caller qualification."""
import copy
import io
import json
import unittest

from blake3 import blake3
from circuits import transfer_rk_binding as binding, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests import test_transfer_authorization_roles as role_fixture


def fixture(rows=None, with_constant=False, reverse_x=False):
    """Reuse the typed role fixture; supply a complete tiny ordinary relation."""
    typed = role_fixture.AuthorizationRoleTests()
    typed.setUp()
    obj, rnk, ivk = copy.deepcopy((typed.obj, typed.rnk, typed.ivk))
    expressions = {tuple(item['source']): item for item in obj['expressions']}
    if with_constant:
        expressions[(2, 22)]['terms'].insert(0, [0, f'{7:064x}'])
    lcs = {source: tuple((column, int(value, 16)) for column, value in item['terms'])
           for source, item in expressions.items()}
    copy_column = obj['constant_copy']
    expected = [canonical([(0, 1), (copy_column, -1)])]
    for axis, left, right in zip(('x', 'y'), obj['spend']['computed'], obj['spend']['rk']):
        terms = combine(lcs[tuple(left['source'])], lcs[tuple(right['source'])], -1)
        expected.append(canonical((copy_column if column == 0 else column,
                                   -value if axis == 'x' and reverse_x else value)
                                  for column, value in terms))
    if rows is None:
        rows = [dict(row=index, a=[[column, f'{value:064x}'] for column, value in terms], b=[])
                for index, terms in enumerate(expected)]
    digest = blake3()
    source_public, source_block = [[1, 900]], [[1, 901]]
    digest.update(relation.NAMESPACE + relation.u64(1024) + relation.u64(len(rows)) +
                  relation.indices(source_public) + relation.u64(1) + relation.indices(source_block))
    for row in rows:
        digest.update(b'A' + relation.terms(row['a'], 1024) + b'B' + relation.terms(row['b'], 1024))
    value = digest.hexdigest()
    obj.update(relation_digest=value, full_rows=len(rows))
    rnk.update(relation_digest=value, full_rows=len(rows))
    ivk.update(relation_digest=value, stored_rows=len(rows))
    header = dict(schema='shieldd-transfer-relation-v1', family='transfer', relation_digest=value,
                  domain_size=1024, stored_rows=len(rows), public_inputs=1, committed_blocks=[1],
                  constant_column=0, public_columns=[1], committed_columns=[[2]],
                  source_public=source_public, source_blocks=[source_block],
                  coefficient_encoding='canonical-big-endian-32', field_modulus=str(relation.MODULUS),
                  role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
                  padding='implicit-all-zero-rows-to-domain-size')
    encode = lambda item: json.dumps(item).encode() + b'\n'
    stream = io.BytesIO(b''.join(map(encode, [header, *rows, dict(eof=True, rows=len(rows))])))
    return encode(obj), stream, value, obj['ivk_handles'], rnk, ivk


def synthetic_candidate():
    """Root may kernel-check this diagnostic candidate; it is never published."""
    data, stream, digest, handles, rnk, ivk = fixture(with_constant=True, reverse_x=True)
    extracted = binding.extract(data, stream, digest, handles, rnk, ivk)
    return binding.generate(data, extracted, digest, handles, rnk, ivk)


class RkBindingTests(unittest.TestCase):
    def inspect(self, **options):
        args = fixture(**options)
        return args, binding.extract(*args)

    def test_exact_ordinary_rows_and_shape(self):
        _, result = self.inspect()
        self.assertEqual(result['roles'], {'constant-copy': 0, 'x': 1, 'y': 2})
        self.assertEqual(result['orientations'], {'x': 'computed-minus-rk', 'y': 'computed-minus-rk'})
        self.assertEqual(len(result['selected_rows']), 3)
        self.assertIn('canonical randomizer', result['scope'])

    def test_outlining_and_negative_assertion_orientation(self):
        _, result = self.inspect(with_constant=True, reverse_x=True)
        self.assertEqual(result['orientations']['x'], 'rk-minus-computed')
        self.assertIn([1000, f'{relation.MODULUS - 7:064x}'], result['selected_rows'][1]['a'])

    def test_missing_or_semantically_changed_equality_refused(self):
        _, baseline = self.inspect()
        for kind in ['missing-x', 'changed-x', 'nonzero-b', 'missing-copy']:
            rows = copy.deepcopy(baseline['selected_rows'])
            if kind == 'missing-x':
                rows.pop(1)
            elif kind == 'changed-x':
                rows[1]['a'][0][1] = f'{2:064x}'
            elif kind == 'nonzero-b':
                rows[1]['b'] = [[450, f'{1:064x}']]
            else:
                rows.pop(0)
            for index, row in enumerate(rows):
                row['row'] = index
            with self.subTest(kind=kind), self.assertRaisesRegex(relation.RelationError, 'missing actual RK binding row'):
                self.inspect(rows=rows)

    def test_complete_digest_identity_cannot_be_skipped(self):
        data, stream, digest, handles, rnk, ivk = fixture()
        raw = stream.getvalue().replace(f'{1:064x}'.encode(), f'{2:064x}'.encode(), 1)
        with self.assertRaisesRegex(relation.RelationError, 'do not match relation digest'):
            binding.extract(data, io.BytesIO(raw), digest, handles, rnk, ivk)

    def test_metadata_shape_mismatch_refused_after_replay(self):
        data, stream, digest, handles, rnk, ivk = fixture()
        obj = json.loads(data)
        obj['full_rows'] = 4
        rnk['full_rows'] = 4
        ivk['stored_rows'] = 4
        with self.assertRaisesRegex(relation.RelationError, 'metadata/full relation shape mismatch'):
            binding.extract(json.dumps(obj).encode() + b'\n', stream, digest, handles, rnk, ivk)

    def test_generator_revalidates_selection_semantics(self):
        args, baseline = self.inspect()
        data, _, digest, handles, rnk, ivk = args
        for kind in ['identity', 'metadata', 'lc', 'orientation', 'row', 'row-bool', 'extra', 'coverage']:
            changed = copy.deepcopy(baseline)
            if kind == 'identity':
                changed['identity']['stored_rows'] = True
            elif kind == 'metadata':
                changed['metadata_sha256'] = '0' * 64
            elif kind == 'lc':
                changed['computed'] = ()
            elif kind == 'orientation':
                changed['orientations']['x'] = 'rk-minus-computed'
            elif kind == 'row':
                changed['selected_rows'][1]['a'][0][1] = f'{2:064x}'
            elif kind == 'row-bool':
                changed['roles']['x'] = True
            elif kind == 'extra':
                changed['selected_rows'][0]['extra'] = None
            else:
                changed['selected_rows'].pop()
            with self.subTest(kind=kind), self.assertRaises(relation.RelationError):
                binding.generate(data, changed, digest, handles, rnk, ivk)

    def test_persisted_extraction_roundtrip_and_typed_lc_refusals(self):
        args, baseline = self.inspect(with_constant=True, reverse_x=True)
        data, _, digest, handles, rnk, ivk = args
        persisted = json.loads(json.dumps(baseline))
        self.assertEqual(binding.generate(data, persisted, digest, handles, rnk, ivk),
                         binding.generate(data, baseline, digest, handles, rnk, ivk))
        for column, coefficient in [(0, True), (0.0, 7), (0, 0), (0, relation.MODULUS), (1024, 1)]:
            changed = copy.deepcopy(persisted)
            changed['computed'][0][0] = [column, coefficient]
            with self.subTest(column=column, coefficient=coefficient), self.assertRaises(relation.RelationError):
                binding.generate(data, changed, digest, handles, rnk, ivk)

    def test_finite_generator_named_signature_and_axiom_audits(self):
        source = synthetic_candidate()
        for name in ['constantLink', 'rk_x_equal', 'rk_y_equal', 'actual_rk_binding']:
            self.assertIn('#check @' + name, source)
            self.assertIn('#print axioms ' + name, source)
        self.assertIn('set_option maxHeartbeats 200000', source)
        self.assertIn('normalized (by decide)).symm', source)
        self.assertIn('namespace ShielddSecurity.RuntimeTransferRkBinding', source)
        self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')

    def test_selected_equality_omission_observes_intended_semantic_failure(self):
        _, result = self.inspect()
        for axis, column in [('x', 422), ('y', 423)]:
            rho = {0: 1, 1000: 1, column: 1}
            evaluate = lambda terms: sum(int(value, 16) * rho.get(col, 0) for col, value in terms) % relation.MODULUS
            rejected = [row['row'] for row in result['selected_rows']
                        if evaluate(row['a']) ** 2 % relation.MODULUS != evaluate(row['b'])]
            self.assertEqual(rejected, [result['roles'][axis]])
            for row in result['selected_rows']:
                if row['row'] != result['roles'][axis]:
                    self.assertEqual(evaluate(row['a']) ** 2 % relation.MODULUS, evaluate(row['b']))
            index = 0 if axis == 'x' else 1
            left = sum(value * rho.get(col, 0) for col, value in result['computed'][index]) % relation.MODULUS
            right = sum(value * rho.get(col, 0) for col, value in result['rk'][index]) % relation.MODULUS
            self.assertNotEqual(left, right)


if __name__ == '__main__':
    unittest.main()
