import copy
import importlib.util
import io
import json
import struct
import unittest
from circuits import transfer_relation as relation


class TransferRelationTests(unittest.TestCase):
    def setUp(self):
        from blake3 import blake3
        # Independently spell the upstream digest preimage for a small row.
        # This fixture tests transport/identity, not production Transfer semantics.
        u64 = lambda value: struct.pack('>Q', value)
        u32 = lambda value: struct.pack('>I', value)
        coefficient = lambda value: value.to_bytes(32, 'big')
        preimage = (b'_COMMONWARE_CRYPTOGRAPHY_ZK_PARI_RELATION_DIGEST'
                    + u64(4) + u64(1) + u64(1) + b'\x01' + u32(0)
                    + u64(1) + u64(1) + b'\x01' + u32(1)
                    + b'A' + u64(2) + u32(0) + coefficient(1) + u32(1) + coefficient(2)
                    + b'B' + u64(1) + u32(2) + coefficient(1))
        self.digest = blake3(preimage).hexdigest()
        self.header = {'schema': 'shieldd-transfer-relation-v1', 'family': 'transfer',
                       'relation_digest': self.digest, 'domain_size': 4, 'stored_rows': 1,
                       'public_inputs': 1, 'committed_blocks': [1], 'constant_column': 0,
                       'public_columns': [1], 'committed_columns': [[2]],
                       'source_public': [[1, 0]], 'source_blocks': [[[1, 1]]],
                       'coefficient_encoding': 'canonical-big-endian-32',
                       'field_modulus': str(relation.MODULUS),
                       'role_provenance': 'constant0/public prefix and committed_start=1+public_count in exact compiler',
                       'padding': 'implicit-all-zero-rows-to-domain-size'}
        self.row = {'row': 0, 'a': [[0, f'{1:064x}'], [1, f'{2:064x}']], 'b': [[2, f'{1:064x}']]}
        self.eof = {'eof': True, 'rows': 1}

    def encoded(self):
        return b''.join(json.dumps(value).encode() + b'\n' for value in [self.header, self.row, self.eof])

    def inspect(self, raw=None, expected=None):
        return relation.inspect(io.BytesIO(self.encoded() if raw is None else raw), expected)

    def test_exact_digest_and_complete_framing(self):
        result = self.inspect(expected=self.digest)
        self.assertEqual(result['relation_digest'], self.digest)
        self.assertEqual(result['stored_rows'], 1)
        self.assertIn('semantic/key/source joins open', result['scope'])

    def test_coefficient_change_rejects_actual_digest(self):
        self.row['a'][1][1] = f'{3:064x}'
        with self.assertRaisesRegex(relation.RelationError, 'relation digest'):
            self.inspect()

    def test_wrong_selected_key_relation_rejects(self):
        with self.assertRaisesRegex(relation.RelationError, 'relation digest'):
            self.inspect(expected='0' * 64)

    def test_public_committed_constant_roles_cannot_swap(self):
        for field, value in [('constant_column', 1), ('public_columns', [2]),
                             ('committed_columns', [[1]]), ('committed_blocks', [2])]:
            with self.subTest(field=field):
                old = self.header[field]
                self.header[field] = value
                with self.assertRaisesRegex(relation.RelationError, 'role layout'):
                    self.inspect()
                self.header[field] = old

    def test_sort_duplicate_column_and_column_range_fail(self):
        for a in [list(reversed(self.row['a'])), [self.row['a'][0], self.row['a'][0]], [[4, f'{1:064x}']]]:
            with self.subTest(a=a):
                self.row['a'] = a
                with self.assertRaisesRegex(relation.RelationError, 'column order/range'):
                    self.inspect()

    def test_out_of_field_and_zero_coefficients_fail(self):
        for value in [0, relation.MODULUS, 2**256 - 1]:
            with self.subTest(value=value):
                self.row['a'][0][1] = f'{value:064x}'
                with self.assertRaisesRegex(relation.RelationError, 'out-of-field coefficient'):
                    self.inspect()

    def test_noncanonical_encoding_fails(self):
        for value in ['01', 'A' * 64, '-1', 1]:
            with self.subTest(value=value):
                self.row['a'][0][1] = value
                with self.assertRaisesRegex(relation.RelationError, 'coefficient encoding'):
                    self.inspect()

    def test_row_order_and_missing_rows_fail(self):
        self.row['row'] = 1
        with self.assertRaisesRegex(relation.RelationError, 'reordered'):
            self.inspect()
        self.row['row'] = 0
        raw = json.dumps(self.header).encode() + b'\n' + json.dumps(self.eof).encode() + b'\n'
        with self.assertRaisesRegex(relation.RelationError, 'unknown row'):
            self.inspect(raw)

    def test_eof_truncation_and_trailing_data_fail(self):
        raw = self.encoded()
        for mutant in [raw[:-1], raw + b'\n', raw + b'{}\n']:
            with self.subTest(mutant=mutant[-20:]):
                with self.assertRaises(relation.RelationError):
                    self.inspect(mutant)
        self.eof['rows'] = 2
        with self.assertRaisesRegex(relation.RelationError, 'EOF'):
            self.inspect()

    def test_source_roles_and_duplicate_keys_fail(self):
        self.header['source_blocks'] = [self.header['source_public']]
        with self.assertRaisesRegex(relation.RelationError, 'source role overlap'):
            self.inspect()
        self.header['source_blocks'] = [[[1, 1]]]
        raw = self.encoded().replace(b'"row": 0', b'"row": 0, "row": 0')
        with self.assertRaisesRegex(relation.RelationError, 'duplicate JSON'):
            self.inspect(raw)

    def test_boolean_integer_alias_fails(self):
        self.row['row'] = False
        with self.assertRaisesRegex(relation.RelationError, 'unsigned integer'):
            self.inspect()

    def test_header_boolean_and_float_aliases_fail(self):
        for field, value in [('public_inputs', True), ('constant_column', 0.0),
                             ('committed_blocks', [True]), ('public_columns', [1.0]),
                             ('committed_columns', [[2.0]])]:
            with self.subTest(field=field):
                old = self.header[field]
                self.header[field] = value
                with self.assertRaisesRegex(relation.RelationError, 'unsigned integer'):
                    self.inspect()
                self.header[field] = old


if __name__ == '__main__':
    unittest.main()
