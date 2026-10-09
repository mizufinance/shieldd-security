"""Synthetic typed boundary-join controls; no runtime or proof evidence.

Accepted inputs model the metadata contract of previously accepted captures.
These fixtures do not qualify an RNK-DH/IVK capture by constructing its digest.
"""
import copy
import hashlib
import json
import unittest

from circuits import transfer_authorization_roles as roles
from circuits.transfer_relation import MODULUS, RelationError


def source(tag, index):
    return {'source': [tag, index]}


def native(value):
    return {'native': f'{value:064x}'}


def encoded(obj):
    return (json.dumps(obj) + '\n').encode()


class AuthorizationRoleTests(unittest.TestCase):
    def setUp(self):
        w = lambda index: source(1, index)
        n = lambda index: source(2, index)
        ivk = [[1, 0], [1, 1], [1, 2], [2, 3]]
        caller = dict(regulated=w(4), asset=w(5), leaf_ring=[w(6), w(7)],
                      fixed_ring=[native(0), native(1)], selected_ring=[n(10), n(11)],
                      address=[w(i) for i in range(8, 12)], rnk_dh=[w(12), w(13)],
                      registered_rnk=w(14), ak=[w(1), w(2)], nk=w(0), effective_nk=n(12))
        spend = dict(ak=caller['ak'], randomizer=w(15), bits=[[1, i] for i in range(100, 352)],
                     generator=[native(0), native(MODULUS - 1)],
                     contribution=[n(20), n(21)], computed=[n(22), n(23)], rk=[w(16), w(17)])
        bindings = dict(inputs=[n(30), n(31)] + caller['address'] + [caller['asset']] + caller['selected_ring'],
                        hash=n(32), commitment=n(33), regulated=caller['regulated'],
                        registered=caller['registered_rnk'], effective_nk=caller['effective_nk'])
        self.obj = dict(schema='shieldd-transfer-authorization-roles-v1', family='transfer', scope=roles.SCOPE,
                        relation_digest='a' * 64, domain_size=1024, full_rows=900, constant_copy=1000,
                        ordinary_full_ordered_rows_equal=True, ivk_handles=ivk,
                        caller=caller, spend=spend, rnk_bindings=bindings)
        handles = {tuple(handle) for handle in ivk + spend['bits']}

        def collect(value):
            if isinstance(value, dict):
                if set(value) == {'source'}:
                    handles.add(tuple(value['source']))
                else:
                    for child in value.values():
                        collect(child)
            elif isinstance(value, list):
                for child in value:
                    collect(child)

        for value in (caller, spend, bindings):
            collect(value)

        def expression(handle):
            tag, index = handle
            column = 3 + index if tag == 1 else 400 + index
            return dict(source=list(handle), terms=[[column, f'{1:064x}']])

        self.obj['expressions'] = [expression(handle) for handle in sorted(handles)]
        shape = dict(relation_digest='a' * 64, domain_size=1024, constant_copy=1000)
        self.rnk = dict(shape, schema='shieldd-transfer-rnk-dh-v1', full_rows=900,
                        ivk_handles=ivk, base=caller['rnk_dh'], rnk_bindings=bindings,
                        expressions=[expression(handle) for handle in [(1, 12), (1, 13), (2, 30), (2, 31)]])
        self.ivk = dict(shape, schema='shieldd-transfer-ivk-inspection-v1', stored_rows=900,
                        handles=ivk, ordinary_full_ordered_rows_equal=True,
                        expressions=[expression(handle) for handle in map(tuple, ivk)])
        # Real captures can contain LCs outside the authorization boundary set.
        self.extra = dict(source=[2, 900], terms=[[950, f'{1:064x}']])
        self.rnk['expressions'].append(copy.deepcopy(self.extra))
        self.ivk['expressions'].append(copy.deepcopy(self.extra))

    def parse(self, obj=None, rnk=None, ivk=None):
        return roles.inspect_metadata(encoded(self.obj if obj is None else obj), 'a' * 64,
                                      self.obj['ivk_handles'], self.rnk if rnk is None else rnk,
                                      self.ivk if ivk is None else ivk)

    def test_valid_typed_boundary_join(self):
        result = self.parse()
        self.assertEqual(len(result['bit_handles']), 252)
        self.assertEqual(result['observed'][(2, 30)], ((430, 1),))
        self.assertEqual(result['metadata_sha256'], hashlib.sha256(encoded(self.obj)).hexdigest())
        self.assertNotIn((2, 900), result['observed'])
        self.assertIn('row/native interpretation joins separate', result['scope'])

    def test_same_source_handle_changed_node_lc_refused(self):
        for accepted, handle in ((self.rnk, [2, 30]), (self.ivk, [2, 3])):
            changed = copy.deepcopy(accepted)
            item = next(item for item in changed['expressions'] if item['source'] == handle)
            item['terms'][0][1] = f'{2:064x}'
            with self.subTest(handle=handle), self.assertRaisesRegex(RelationError, 'shared source LC mismatch'):
                self.parse(rnk=changed) if accepted is self.rnk else self.parse(ivk=changed)

    def test_accepted_pair_shared_nonboundary_lc_conflict_refused(self):
        changed = copy.deepcopy(self.ivk)
        changed['expressions'][-1]['terms'][0][1] = f'{2:064x}'
        with self.assertRaisesRegex(RelationError, 'shared source LC mismatch'):
            self.parse(ivk=changed)

    def test_required_accepted_lc_coverage(self):
        for name, original, handle in [('RNK', self.rnk, [1, 12]), ('RNK', self.rnk, [2, 30]),
                                       ('IVK', self.ivk, [1, 0]), ('IVK', self.ivk, [2, 3])]:
            changed = copy.deepcopy(original)
            changed['expressions'] = [item for item in changed['expressions'] if item['source'] != handle]
            with self.subTest(name=name, handle=handle), self.assertRaisesRegex(RelationError, name + ' authorization role expression coverage'):
                self.parse(rnk=changed) if name == 'RNK' else self.parse(ivk=changed)

    def test_exact_accepted_relation_shape(self):
        for name, original, row_key in [('RNK', self.rnk, 'full_rows'), ('IVK', self.ivk, 'stored_rows')]:
            for key, value in [('relation_digest', 'b' * 64), ('domain_size', 2048),
                               (row_key, 901), ('constant_copy', 999)]:
                changed = copy.deepcopy(original)
                changed[key] = value
                with self.subTest(name=name, key=key), self.assertRaisesRegex(RelationError, name + ' relation shape mismatch'):
                    self.parse(rnk=changed) if name == 'RNK' else self.parse(ivk=changed)
            for key in ['domain_size', row_key, 'constant_copy']:
                for value in [True, 1024.0, '1024', None, -1]:
                    changed = copy.deepcopy(original)
                    changed[key] = value
                    with self.subTest(name=name, key=key, value=value), self.assertRaisesRegex(RelationError, 'noncanonical unsigned integer'):
                        self.parse(rnk=changed) if name == 'RNK' else self.parse(ivk=changed)

    def test_accepted_ivk_identity_and_roles(self):
        for name, original, key in [('RNK', self.rnk, 'ivk_handles'), ('IVK', self.ivk, 'handles')]:
            changed = copy.deepcopy(original)
            changed[key][0] = [1, 99]
            with self.subTest(name=name), self.assertRaisesRegex(RelationError, name + ' IVK role mismatch'):
                self.parse(rnk=changed) if name == 'RNK' else self.parse(ivk=changed)
        for identity in [False, 1, None]:
            changed = copy.deepcopy(self.ivk)
            changed['ordinary_full_ordered_rows_equal'] = identity
            with self.subTest(identity=identity), self.assertRaisesRegex(RelationError, 'IVK ordinary identity mismatch'):
                self.parse(ivk=changed)

    def test_optional_ivk_omission_is_refused(self):
        with self.assertRaisesRegex(RelationError, 'accepted IVK role metadata required'):
            roles.inspect_metadata(encoded(self.obj), 'a' * 64, self.obj['ivk_handles'], self.rnk)

    def test_accepted_rnk_references_do_not_alias_python_booleans(self):
        for kind in ['base', 'bindings', 'extra', 'malformed']:
            changed = copy.deepcopy(self.rnk)
            if kind == 'base':
                changed['base'][0]['source'][0] = True
                reason = 'noncanonical unsigned integer'
            elif kind == 'bindings':
                changed['rnk_bindings']['inputs'][2]['source'][0] = True
                reason = 'noncanonical unsigned integer'
            elif kind == 'extra':
                changed['rnk_bindings']['extra'] = 0
                reason = 'accepted RNK bindings closed shape mismatch'
            else:
                changed['rnk_bindings']['inputs'] = None
                reason = 'wrong authorization role array shape'
            with self.subTest(kind=kind), self.assertRaisesRegex(RelationError, reason):
                self.parse(rnk=changed)

    def test_all_accepted_expressions_validated_even_nonshared(self):
        cases = [None, {}, [], [{'source': [2, 900]}], [None],
                 [{'source': [2, 900], 'terms': [[950, 'bad']]}],
                 [{'source': [2, 900], 'terms': [[950, f'{0:064x}']]}],
                 [{'source': [2, 900], 'terms': [[1000, f'{1:064x}']]}],
                 [{'source': [1, 900], 'terms': [[950, f'{1:064x}']]}],
                 [{'source': [0, 900], 'terms': [[950, f'{1:064x}']]}]]
        for name, original in [('RNK', self.rnk), ('IVK', self.ivk)]:
            for expressions in cases:
                changed = copy.deepcopy(original)
                changed['expressions'] = expressions
                with self.subTest(name=name, expressions=expressions), self.assertRaises(RelationError):
                    self.parse(rnk=changed) if name == 'RNK' else self.parse(ivk=changed)
            for mutation in ['duplicate', 'reverse', 'extra-key', 'overflow']:
                changed = copy.deepcopy(original)
                if mutation == 'duplicate':
                    changed['expressions'].append(copy.deepcopy(changed['expressions'][-1]))
                elif mutation == 'reverse':
                    changed['expressions'].reverse()
                elif mutation == 'extra-key':
                    changed['expressions'][-1]['extra'] = 0
                else:
                    changed['expressions'] = [copy.deepcopy(self.extra)] * 4097
                with self.subTest(name=name, mutation=mutation), self.assertRaises(RelationError):
                    self.parse(rnk=changed) if name == 'RNK' else self.parse(ivk=changed)

    def test_randomizer_is_252_distinct_witness_bits(self):
        for kind, reason in [('short', 'bit length'), ('duplicate', 'distinct witnesses'),
                             ('node', 'distinct witnesses'), ('bool', 'noncanonical unsigned integer')]:
            obj = copy.deepcopy(self.obj)
            if kind == 'short':
                obj['spend']['bits'].pop()
            elif kind == 'duplicate':
                obj['spend']['bits'][1] = obj['spend']['bits'][0]
            elif kind == 'node':
                obj['spend']['bits'][0][0] = 2
            else:
                obj['spend']['bits'][0][1] = True
            with self.subTest(kind=kind), self.assertRaisesRegex(RelationError, reason):
                self.parse(obj)

    def test_native_values_are_canonical_field_elements(self):
        for target in ['fixed_ring', 'generator']:
            for value in [MODULUS, -1, 'A' * 64, '0' * 63, 0, True, None]:
                obj = copy.deepcopy(self.obj)
                owner = obj['caller'] if target == 'fixed_ring' else obj['spend']
                owner[target][0] = {'native': f'{value:064x}' if type(value) is int and value != 0 else value}
                with self.subTest(target=target, value=value), self.assertRaisesRegex(RelationError, 'noncanonical native'):
                    self.parse(obj)
            obj = copy.deepcopy(self.obj)
            owner = obj['caller'] if target == 'fixed_ring' else obj['spend']
            owner[target][0] = source(1, 0)
            with self.assertRaisesRegex(RelationError, 'noncanonical native'):
                self.parse(obj)

    def test_authorization_expressions_have_exact_coverage(self):
        for kind, reason in [('missing', 'coverage mismatch'), ('extra', 'coverage mismatch'),
                             ('duplicate', 'unordered/duplicate'), ('outline', 'outline mismatch'),
                             ('witness', 'witness/column mismatch')]:
            obj = copy.deepcopy(self.obj)
            if kind == 'missing':
                obj['expressions'].pop()
            elif kind == 'extra':
                obj['expressions'].append(copy.deepcopy(self.extra))
            elif kind == 'duplicate':
                obj['expressions'].append(copy.deepcopy(obj['expressions'][-1]))
            elif kind == 'outline':
                obj['expressions'][-1]['terms'] = [[1000, f'{1:064x}']]
            else:
                obj['expressions'][0]['terms'][0][1] = f'{2:064x}'
            with self.subTest(kind=kind), self.assertRaisesRegex(RelationError, reason):
                self.parse(obj)

    def test_closed_source_roles_and_caller_bindings(self):
        for kind, reason in [('native', 'must be Source'), ('malformed', 'malformed authorization role reference'),
                             ('caller', 'caller/RNK source role mismatch'), ('ak', 'AK or NK mismatch'),
                             ('rnk', 'accepted RNK bindings mismatch'), ('extra', 'closed shape mismatch')]:
            obj = copy.deepcopy(self.obj)
            if kind == 'native':
                obj['caller']['asset'] = native(0)
            elif kind == 'malformed':
                obj['spend']['randomizer'] = {'source': [1, 15], 'native': f'{0:064x}'}
            elif kind == 'caller':
                obj['caller']['rnk_dh'][0] = source(1, 99)
            elif kind == 'ak':
                obj['spend']['ak'][0] = source(1, 99)
            elif kind == 'rnk':
                obj['rnk_bindings']['hash'] = source(2, 99)
            else:
                obj['spend']['extra'] = 0
            with self.subTest(kind=kind), self.assertRaisesRegex(RelationError, reason):
                self.parse(obj)

    def test_malformed_metadata_is_relation_error(self):
        for data in [b'{}', b'[]\n', b'{"schema":1,"schema":2}\n', b'\xff\n',
                     b'{}\n{}\n', b' ' * (2 * 1024 * 1024 + 1), None, '{}\n',
                     b'{"deep":' + b'[' * 2000 + b'0' + b']' * 2000 + b'}\n']:
            with self.subTest(data_type=type(data).__name__), self.assertRaises(RelationError):
                roles.inspect_metadata(data, 'a' * 64, self.obj['ivk_handles'], self.rnk, self.ivk)
        for key, value in [('caller', []), ('spend', None), ('rnk_bindings', None),
                           ('ivk_handles', {}), ('domain_size', True), ('full_rows', 0),
                           ('constant_copy', 2), ('ordinary_full_ordered_rows_equal', 1),
                           ('schema', 'other'), ('scope', 'other'), ('relation_digest', 'b' * 64)]:
            obj = copy.deepcopy(self.obj)
            obj[key] = value
            with self.subTest(key=key), self.assertRaises(RelationError):
                self.parse(obj)
        for original in [self.rnk, self.ivk]:
            for key in ['domain_size', 'constant_copy', 'expressions']:
                changed = copy.deepcopy(original)
                changed.pop(key)
                with self.subTest(original=original['schema'], key=key), self.assertRaises(RelationError):
                    self.parse(rnk=changed) if original is self.rnk else self.parse(ivk=changed)

    def test_digest_and_ivk_handle_inputs_are_strict(self):
        for digest in [None, True, 'A' * 64, 'short']:
            with self.subTest(digest=digest), self.assertRaisesRegex(RelationError, 'exact authorization role relation'):
                roles.inspect_metadata(encoded(self.obj), digest, self.obj['ivk_handles'], self.rnk, self.ivk)
        for handles in [None, {}, [], [[1, 0]] * 4, [[0, 0], [1, 1], [1, 2], [2, 3]],
                        [[True, 0], [1, 1], [1, 2], [2, 3]]]:
            with self.subTest(handles=handles), self.assertRaises(RelationError):
                roles.inspect_metadata(encoded(self.obj), 'a' * 64, handles, self.rnk, self.ivk)


if __name__ == '__main__':
    unittest.main()
