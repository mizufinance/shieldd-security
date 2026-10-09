import copy
import io
import json
import unittest

from circuits.transfer_source_program import FIELD_MODULUS, ProgramError, inspect_stream


class CompleteProgramReaderTests(unittest.TestCase):
    def records(self):
        return [dict(schema='shieldd-transfer-source-program-v1', family='transfer',
                     witnesses=2, constants=1, nodes=2, assertions=1,
                     field_modulus=str(FIELD_MODULUS), coefficient_encoding='canonical-big-endian-32',
                     source_public=[[2, 1]], source_blocks=[[[1, 0]]]),
                {'constant': 0, 'value': '0'*63+'1'},
                {'node': 0, 'operation': 'add', 'left': [1, 0], 'right': [0, 0]},
                {'node': 1, 'operation': 'mul', 'left': [2, 0], 'right': [1, 1]},
                {'assertion': 0, 'left': [2, 1], 'right': [1, 0]},
                {'end': True, 'constants': 1, 'nodes': 2, 'assertions': 1}]

    def stream(self, records):
        return io.BytesIO(('\n'.join(json.dumps(x) for x in records)+'\n').encode())

    def test_complete_stream_and_callback_preserve_every_record(self):
        rows = self.records()
        seen = []
        report = inspect_stream(self.stream(rows), seen.append)
        self.assertEqual(seen, rows[:-1])
        self.assertEqual(report['records'], len(rows))
        self.assertEqual(report['counts'], dict(witnesses=2, constants=1, nodes=2, assertions=1))
        self.assertFalse(report['full_row_correspondence'])
        self.assertEqual(report['proof_or_semantic_control_credit'], 0)

    def test_truncation_reordering_and_trailing_records_rejected(self):
        original = self.records()
        variants = [original[:-1], original[:3]+original[4:], original+original[-1:]]
        moved = copy.deepcopy(original)
        moved[2], moved[3] = moved[3], moved[2]
        variants.append(moved)
        for rows in variants:
            with self.subTest(rows=rows), self.assertRaises(ProgramError):
                inspect_stream(self.stream(rows))

    def test_cycles_unknown_indices_and_out_of_range_rejected(self):
        for index in [[2, 0], [2, 1], [3, 0], [1, 2], [0, 1], [1, -1], [True, 0]]:
            rows = self.records()
            rows[2]['left'] = index
            with self.subTest(index=index), self.assertRaises(ProgramError):
                inspect_stream(self.stream(rows))

    def test_noncanonical_constants_and_wrong_schema_rejected(self):
        for value in [f'{FIELD_MODULUS:064x}', '0'*63, 'z'*64]:
            rows = self.records()
            rows[1]['value'] = value
            with self.subTest(value=value), self.assertRaises(ProgramError):
                inspect_stream(self.stream(rows))
        rows = self.records()
        rows[0]['selected_slice'] = True
        with self.assertRaises(ProgramError):
            inspect_stream(self.stream(rows))

    def test_alias_roles_and_false_counts_rejected(self):
        for field, value in [('source_public', [[1, 0]]), ('nodes', True), ('nodes', 3)]:
            rows = self.records()
            rows[0][field] = value
            with self.subTest(field=field), self.assertRaises(ProgramError):
                inspect_stream(self.stream(rows))

    def test_duplicate_keys_boolean_end_counts_and_callback_mutation(self):
        raw = self.stream(self.records()).getvalue().replace(b'"witnesses": 2',
            b'"witnesses": 3, "witnesses": 2')
        with self.assertRaises(ProgramError):
            inspect_stream(io.BytesIO(raw))
        rows = self.records()
        rows[-1]['constants'] = True
        with self.assertRaises(ProgramError):
            inspect_stream(self.stream(rows))
        def mutate(item):
            if 'witnesses' in item:
                item['nodes'] = 0
                item['source_public'][0][1] = 100
        report = inspect_stream(self.stream(self.records()), mutate)
        self.assertEqual(report['counts']['nodes'], 2)
        self.assertEqual(report['source_public'], [[2, 1]])


if __name__ == '__main__':
    unittest.main()
