import copy
import io
import json
import struct
import tempfile
import unittest
from pathlib import Path

from blake3 import blake3
from circuits.transfer_relation import MODULUS as P, NAMESPACE, RelationError, inspect, indices, u64
from circuits.transfer_program_lowering import compare_stream, select_stream
from circuits.transfer_source_program import ProgramError
from circuits.transfer_spool import SpoolJSONL, load_shape
from circuits.transfer_certificate_export import export_database, verify_export


ROWS = [([(3, 1), (4, P-1)], [(6, 1)]),
        ([(3, 1), (4, 1)], [(5, 4), (6, 1)]),
        ([(1, 1), (3, P-1)], []), ([(2, 1), (4, P-1)], []),
        ([(0, 1), (7, P-1)], [])]


def fixture(rows=ROWS):
    raw = b''
    digest = blake3(NAMESPACE + u64(8) + u64(len(rows)) + indices([[1, 0]])
                    + u64(1) + indices([[1, 1]]))
    for a, b in rows:
        for marker, terms in [(b'A', a), (b'B', b)]:
            encoded = u64(len(terms)) + b''.join(struct.pack('>I', col)
                       + value.to_bytes(32, 'big') for col, value in terms)
            raw += encoded
            digest.update(marker + encoded)
    shape = dict(schema='shieldd-transfer-ordered-spool-v1', domain_size=8,
                 relation_digest=digest.hexdigest(), full_rows=len(rows), public_inputs=1,
                 blocks=[1], source_public=[[1, 0]], source_blocks=[[[1, 1]]], compilation='ordinary')
    return raw, shape


def program():
    records = [dict(schema='shieldd-transfer-source-program-v1', family='transfer',
        witnesses=2, constants=0, nodes=1, assertions=0, field_modulus=str(P),
        coefficient_encoding='canonical-big-endian-32', source_public=[[1, 0]],
        source_blocks=[[[1, 1]]]), dict(node=0, operation='mul', left=[1, 0], right=[1, 1]),
        dict(end=True, constants=0, nodes=1, assertions=0)]
    return io.BytesIO(('\n'.join(json.dumps(x) for x in records)+'\n').encode())


class SpoolTests(unittest.TestCase):
    def inspect(self, raw, shape):
        return inspect(SpoolJSONL(io.BytesIO(raw), shape))

    def test_literal_binary_rows_roundtrip_and_digest(self):
        raw, shape = fixture()
        seen = []
        adapter = SpoolJSONL(io.BytesIO(raw), shape, seen.append)
        identity = inspect(adapter, shape['relation_digest'])
        self.assertEqual(identity['stored_rows'], 5)
        self.assertEqual([[(c, int(v, 16)) for c, v in row['a']] for row in seen],
                         [a for a, b in ROWS])
        self.assertTrue(adapter.receipt()['completed'])
        self.assertEqual(adapter.receipt()['binary_bytes'], len(raw))

    def test_actual_comparator_accepts_independent_literal_rows(self):
        with tempfile.TemporaryDirectory() as directory:
            db = Path(directory)/'fresh.sqlite'
            select_stream(program(), db)
            raw, shape = fixture()
            result = compare_stream(SpoolJSONL(io.BytesIO(raw), shape), db, shape['relation_digest'])
            self.assertEqual(result['ordered_row_body_comparisons'], 5)
            self.assertEqual(result['proof_credit'], 0)

    def test_rehashed_each_row_body_mutation_rejected_by_comparison(self):
        with tempfile.TemporaryDirectory() as directory:
            db = Path(directory)/'fresh.sqlite'
            select_stream(program(), db)
            for ordinal in range(5):
                rows = copy.deepcopy(ROWS)
                col, value = rows[ordinal][0][0]
                rows[ordinal][0][0] = (col, value+1)
                raw, shape = fixture(rows)
                # The mutation has a valid digest and well-formed rows. It must
                # fail the exact compiler body comparison, not identity/framing.
                self.assertEqual(self.inspect(raw, shape)['relation_digest'], shape['relation_digest'])
                with self.subTest(row=ordinal), self.assertRaisesRegex(ProgramError, 'row .* changed'):
                    compare_stream(SpoolJSONL(io.BytesIO(raw), shape), db)

    def test_truncation_at_each_first_row_component(self):
        raw, shape = fixture()
        for size in [0, 7, 8, 11, 43, 79, len(raw)-1]:
            with self.subTest(size=size), self.assertRaisesRegex(RelationError, 'truncated'):
                self.inspect(raw[:size], shape)

    def test_trailing_data_rejected(self):
        raw, shape = fixture()
        with self.assertRaisesRegex(RelationError, 'trailing'):
            self.inspect(raw+b'\x00', shape)

    def test_count_bound_before_operand_allocation(self):
        _, shape = fixture()
        with self.assertRaisesRegex(RelationError, 'term count'):
            self.inspect(struct.pack('>Q', 2**64-1), shape)

    def test_zero_and_noncanonical_field_coefficients(self):
        raw, shape = fixture()
        for value in [0, P, 2**256-1]:
            changed = raw[:12] + value.to_bytes(32, 'big') + raw[44:]
            with self.subTest(value=value), self.assertRaisesRegex(RelationError, 'coefficient'):
                self.inspect(changed, shape)

    def test_column_out_of_range_duplicate_and_order(self):
        raw, shape = fixture()
        for offset, value in [(8, 8), (44, 3), (44, 2)]:
            changed = raw[:offset]+struct.pack('>I', value)+raw[offset+4:]
            with self.subTest(offset=offset,value=value), self.assertRaisesRegex(RelationError, 'column'):
                self.inspect(changed, shape)

    def test_shape_roles_counts_types_schema_and_domains_rejected(self):
        raw, shape = fixture()
        changes = [('domain_size', 7), ('domain_size', 2**23), ('full_rows', 9),
                   ('full_rows', True), ('public_inputs', True), ('blocks', [True]),
                   ('source_public', [[True, 0]]), ('source_public', [[1, 1]]),
                   ('source_blocks', [[[0, 1]]]), ('schema', 'other'), ('compilation', 'observer')]
        for key, value in changes:
            bad = copy.deepcopy(shape); bad[key] = value
            with self.subTest(key=key,value=value), self.assertRaises(RelationError):
                self.inspect(raw, bad)

    def test_declared_count_mismatch_rejected_in_both_directions(self):
        raw, shape = fixture()
        for count, error in [(4, 'trailing'), (6, 'truncated')]:
            bad = dict(shape, full_rows=count)
            with self.subTest(count=count), self.assertRaisesRegex(RelationError,error):
                self.inspect(raw, bad)

    def test_duplicate_unknown_and_overlong_shape(self):
        _, shape = fixture()
        raw = json.dumps(shape).encode()
        for encoded in [raw[:-1]+b',"public_inputs":1}', b'x'*65537,
                        json.dumps(dict(shape, extra=1)).encode()]:
            with self.assertRaises(RelationError):
                load_shape(io.BytesIO(encoded))

    def test_snapshot_shape_and_partial_receipt(self):
        raw, shape = fixture()
        adapter = SpoolJSONL(io.BytesIO(raw), shape)
        shape['source_public'][0][1] = 99
        with self.assertRaisesRegex(RelationError,'incomplete'):
            adapter.receipt()
        self.assertEqual(inspect(adapter)['source_public'], [[1,0]])

    def test_wrong_digest_and_json_record_limit(self):
        raw, shape = fixture()
        with self.assertRaisesRegex(RelationError,'digest'):
            self.inspect(raw, dict(shape,relation_digest='0'*64))
        with self.assertRaisesRegex(RelationError,'bounded'):
            SpoolJSONL(io.BytesIO(raw), shape).readline(1)

    def test_complete_certificate_callback_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            db=Path(directory)/'selection.sqlite'; output=Path(directory)/'certificates.gz'
            select_stream(program(),db)
            exported=export_database(db,output)
            verified=verify_export(output)
            self.assertEqual(exported['counts'],dict(node=1,assertion=0,column=8,row=5))
            self.assertEqual(exported['raw_sha256'],verified['raw_sha256'])
            with self.assertRaisesRegex(ProgramError,'fresh'):
                export_database(db,output)

    def test_partial_or_missing_certificate_table_refused(self):
        import sqlite3
        with tempfile.TemporaryDirectory() as directory:
            db=Path(directory)/'selection.sqlite'
            select_stream(program(),db)
            with sqlite3.connect(db) as connection:
                connection.execute('DELETE FROM nodes WHERE id=0')
            with self.assertRaisesRegex(ProgramError,'table'):
                export_database(db,Path(directory)/'certificates.gz')

    def test_truncated_certificate_export_rejected(self):
        import gzip
        with tempfile.TemporaryDirectory() as directory:
            db=Path(directory)/'selection.sqlite'; output=Path(directory)/'certificates.gz'
            select_stream(program(),db)
            export_database(db,output)
            payload=gzip.decompress(output.read_bytes())
            output.write_bytes(gzip.compress(payload.rsplit(b'\n',2)[0]+b'\n'))
            with self.assertRaisesRegex(ProgramError,'complete'):
                verify_export(output)


if __name__ == '__main__':
    unittest.main()
