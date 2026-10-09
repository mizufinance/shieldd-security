import io
import json
import tempfile
import struct
import unittest
from pathlib import Path

from circuits.transfer_program_lowering import compare_stream, select_stream
from circuits.transfer_source_program import FIELD_MODULUS as P, ProgramError


class FullProgramLoweringTests(unittest.TestCase):
    def packet(self, nodes, assertions, constants=(), public=(1, 0), committed=(1, 1)):
        rows = [dict(schema='shieldd-transfer-source-program-v1', family='transfer',
                     witnesses=2, constants=len(constants), nodes=len(nodes),
                     assertions=len(assertions), field_modulus=str(P),
                     coefficient_encoding='canonical-big-endian-32',
                     source_public=[list(public)], source_blocks=[[list(committed)]])]
        rows += [dict(constant=i, value=f'{value:064x}') for i, value in enumerate(constants)]
        rows += [dict(node=i, operation=op, left=list(left), right=list(right))
                 for i, (op, left, right) in enumerate(nodes)]
        rows += [dict(assertion=i, left=list(left), right=list(right))
                 for i, (left, right) in enumerate(assertions)]
        rows += [dict(end=True, constants=len(constants), nodes=len(nodes), assertions=len(assertions))]
        return io.BytesIO(('\n'.join(json.dumps(row) for row in rows)+'\n').encode())

    def select(self, *args, **kwargs):
        selected = []
        with tempfile.TemporaryDirectory() as directory:
            report = select_stream(self.packet(*args, **kwargs), Path(directory)/'program.sqlite', selected.append)
        return report, selected

    def rows(self, selected):
        return [(record['a'], record['b']) for record in selected if record['kind'] == 'row']

    def test_general_product_has_exact_two_rows_and_input_copy_rows(self):
        report, selected = self.select([('mul', (1, 0), (1, 1))], [])
        self.assertEqual(self.rows(selected), [
            (((3, 1), (4, P-1)), ((6, 1),)),
            (((3, 1), (4, 1)), ((5, 4), (6, 1))),
            (((1, 1), (3, P-1)), ()),
            (((2, 1), (4, P-1)), ()),
            (((0, 1), (7, P-1)), ())])
        self.assertEqual((report['stored_rows'], report['constant_copy'], report['domain_size']), (5, 7, 8))
        self.assertFalse(report['ordinary_full_row_comparison'])
        self.assertEqual(report['proof_credit'], 0)

    def test_constant_folding_and_cancellation_retain_source_nodes(self):
        report, selected = self.select([
            ('mul', (1, 0), (0, 0)), ('mul', (0, 1), (1, 1)),
            ('add', (2, 0), (2, 1))], [], constants=(2, P-2), public=(2, 2))
        nodes = [record for record in selected if record['kind'] == 'node']
        self.assertEqual([record['certificate']['constructor'] for record in nodes],
                         ['foldedRight', 'foldedLeft', 'add'])
        self.assertEqual(nodes[-1]['terms'], [[3, 2], [4, P-2]])
        self.assertEqual(report['stored_rows'], 3)

    def test_single_use_square_fuses_but_selected_output_materializes(self):
        nodes = [('mul', (1, 0), (1, 0))]
        assertions = [((2, 0), (1, 1))]
        _, selected = self.select(nodes, assertions)
        self.assertEqual(self.rows(selected)[0], (((3, 1),), ((4, 1),)))
        self.assertEqual(selected[1]['expression_kind'], 'square')
        _, selected = self.select(nodes, assertions, public=(2, 0))
        self.assertEqual(self.rows(selected)[:2], [(((3, 1),), ((5, 1),)),
            (((4, P-1), (5, 1)), ())])
        self.assertEqual(selected[1]['expression_kind'], 'linear')

    def test_both_deferred_squares_materialize_opposite_side_without_zero_placeholder(self):
        nodes = [('mul', (1, 0), (1, 0)), ('mul', (1, 1), (1, 1))]
        for assertion, expected in [(((2, 0), (2, 1)), [(((4, 1),), ((5, 1),)), (((3, 1),), ((5, 1),))]),
                                    (((2, 1), (2, 0)), [(((3, 1),), ((5, 1),)), (((4, 1),), ((5, 1),))])]:
            with self.subTest(assertion=assertion):
                _, selected = self.select(nodes, [assertion])
                self.assertEqual(self.rows(selected)[:2], expected)
                node_records = [x for x in selected if x['kind'] == 'node']
                self.assertEqual(sorted(x['expression_kind'] for x in node_records), ['linear', 'square'])
                self.assertEqual(sorted(x['certificate']['constructor'] for x in node_records), ['deferred', 'square'])
                assertion_record = next(x for x in selected if x['kind'] == 'assertion')
                self.assertEqual(assertion_record['certificate']['rows'], [1])
                materialized = next(x for x in selected if x['kind'] == 'row')
                self.assertEqual(materialized['origin']['kind'], 'node')
                self.assertEqual(materialized['origin']['id'], assertion[1][1])

    def test_repeated_assertion_side_prevents_defer_and_keeps_all_assertions(self):
        report, selected = self.select([('mul', (1, 0), (1, 0))], [((2, 0), (2, 0))])
        self.assertEqual(self.rows(selected)[:2], [(((3, 1),), ((5, 1),)), ((), ())])
        self.assertEqual(report['selected_assertions'], 1)
        self.assertEqual(selected[1]['certificate']['constructor'], 'square')

    def test_outline_rewrites_constants_only_before_final_copy_row(self):
        _, selected = self.select([('add', (1, 0), (0, 0))], [], constants=(7,), public=(2, 0))
        self.assertEqual(self.rows(selected), [
            (((1, 1), (3, P-1), (5, P-7)), ()),
            (((2, 1), (4, P-1)), ()), (((0, 1), (5, P-1)), ())])
        self.assertEqual(selected[1]['terms'], [[0, 7], [3, 1]])

    def test_truncated_program_never_returns_completed_selection_and_reuse_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'program.sqlite'
            raw = self.packet([], []).getvalue()
            with self.assertRaises(ProgramError):
                select_stream(io.BytesIO(raw.rsplit(b'\n', 2)[0]+b'\n'), path)
            with self.assertRaisesRegex(ProgramError, 'fresh'):
                select_stream(io.BytesIO(raw), path)

    def ordinary(self, rows, public=((1, 0),), domain=8):
        from blake3 import blake3
        u64 = lambda value: struct.pack('>Q', value)
        index_bytes = lambda refs: u64(len(refs)) + b''.join(
            bytes([kind]) + struct.pack('>I', index) for kind, index in refs)
        preimage = (b'_COMMONWARE_CRYPTOGRAPHY_ZK_PARI_RELATION_DIGEST' + u64(domain)
                    + u64(len(rows)) + index_bytes(public) + u64(1) + index_bytes([(1, 1)]))
        for a, b in rows:
            for marker, terms in [(b'A', a), (b'B', b)]:
                preimage += marker + u64(len(terms)) + b''.join(
                    struct.pack('>I', column) + value.to_bytes(32, 'big') for column, value in terms)
        header = dict(schema='shieldd-transfer-relation-v1', family='transfer',
                      relation_digest=blake3(preimage).hexdigest(), domain_size=domain,
                      stored_rows=len(rows), public_inputs=1, committed_blocks=[1],
                      constant_column=0, public_columns=[1], committed_columns=[[2]],
                      source_public=list(map(list, public)), source_blocks=[[[1, 1]]],
                      coefficient_encoding='canonical-big-endian-32', field_modulus=str(P),
                      role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
                      padding='implicit-all-zero-rows-to-domain-size')
        records = [header] + [dict(row=i, a=[[c, f'{v:064x}'] for c, v in a],
                                  b=[[c, f'{v:064x}'] for c, v in b]) for i, (a, b) in enumerate(rows)]
        records.append(dict(eof=True, rows=len(rows)))
        return io.BytesIO(('\n'.join(json.dumps(row) for row in records)+'\n').encode())

    def test_every_row_compared_and_valid_rehashed_body_changes_rejected(self):
        expected = [(((3, 1), (4, P-1)), ((6, 1),)),
                    (((3, 1), (4, 1)), ((5, 4), (6, 1))),
                    (((1, 1), (3, P-1)), ()), (((2, 1), (4, P-1)), ()),
                    (((0, 1), (7, P-1)), ())]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'program.sqlite'
            select_stream(self.packet([('mul', (1, 0), (1, 1))], []), path)
            report = compare_stream(self.ordinary(expected), path)
            self.assertEqual(report['ordered_row_body_comparisons'], 5)
            self.assertFalse(report['kernel_run'])
            for ordinal in range(len(expected)):
                changed = list(expected)
                a, b = changed[ordinal]
                changed[ordinal] = (a[:-1]+((a[-1][0], a[-1][1]-1 or 2),), b)
                with self.subTest(ordinal=ordinal), self.assertRaisesRegex(ProgramError, 'changed'):
                    compare_stream(self.ordinary(changed), path)
            for rows, public, domain in [(expected[:-1], ((1, 0),), 8),
                                         (expected, ((2, 0),), 8),
                                         (expected, ((1, 0),), 16)]:
                with self.subTest(public=public, domain=domain), self.assertRaises(ProgramError):
                    compare_stream(self.ordinary(rows, public, domain), path)

    def test_partial_callback_failure_cannot_be_compared_and_committed_constant_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'partial.sqlite'
            def failed_callback(record):
                raise RuntimeError('fixture consumer failed')
            with self.assertRaises(RuntimeError):
                select_stream(self.packet([], []), path, failed_callback)
            with self.assertRaisesRegex(ProgramError, 'incomplete'):
                compare_stream(io.BytesIO(b''), path)
            with self.assertRaisesRegex(ProgramError, 'committed constant'):
                select_stream(self.packet([], [], constants=(1,), committed=(0, 0)),
                              Path(directory)/'invalid-layout.sqlite')

    def test_consumer_mutation_cannot_change_selection_identity_or_role_columns(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'program.sqlite'
            seen = []
            def mutate(record):
                if record['kind'] == 'header':
                    record['source_identity']['source_public'][0][1] = 99
                if record['kind'] == 'column' and record['column'] == 1:
                    record['source']['reference'][1] = 77
                seen.append(record)
            report = select_stream(self.packet([], []), path, mutate)
            self.assertEqual(report['source_identity']['source_public'], [[1, 0]])
            expected = [(((1, 1), (3, P-1)), ()), (((2, 1), (4, P-1)), ()),
                        (((0, 1), (5, P-1)), ())]
            self.assertEqual(compare_stream(self.ordinary(expected), path)['ordered_row_body_comparisons'], 3)


if __name__ == '__main__':
    unittest.main()
