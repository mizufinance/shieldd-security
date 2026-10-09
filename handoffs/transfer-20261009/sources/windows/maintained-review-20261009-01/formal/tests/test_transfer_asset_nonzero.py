"""Exact pinned row-boundary refusal and semantic omission tests.

Fixtures are synthetic copies of the four ordinary rows; the real full stream
check is a separate diagnostic operation, and Lean remains a separate check.
"""
import copy
import hashlib
import io
import json
import re
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from circuits import transfer_asset_nonzero as asset
from circuits.transfer_relation import RelationError


def fixture():
    p = 52435875175126190479447740508185965837690552500527637822603658699938581184513

    def terms(*pairs):
        return [[column, f'{coefficient % p:064x}'] for column, coefficient in pairs]

    return dict(
        schema='shieldd-transfer-asset-nonzero-rows-v1', scope=asset.SCOPE,
        identity=dict(schema='shieldd-transfer-relation-v1', domain_size=262144,
                      stored_rows=200770,
                      relation_digest='16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236',
                      raw_sha256='fa0de5dba3cc2b75ea56e333d2c60f8b373f0c59f6f9b4aed04fd2f59b7f2c9f',
                      source_public=[[1, 22734]], source_blocks=[[[1, 6]]],
                      scope='serialized relation identity and shape only; semantic/key/source joins open'),
        selected_rows=[
            dict(row=27052, a=terms((6, -1), (1992, 1)), b=terms((49791, 1))),
            dict(row=27053, a=terms((6, 1), (1992, 1)), b=terms((49790, 4), (49791, 1))),
            dict(row=179944, a=terms((49790, -1), (200692, 1)), b=[]),
            dict(row=200769, a=terms((0, 1), (200692, -1)), b=[]),
        ])


class AssetBoundaryTests(unittest.TestCase):
    def test_generator_uses_actual_rows_and_checked_compiler_transport(self):
        source = asset.generate(fixture())
        self.assertIn('import ShielddSecurity.Compiler\n', source)
        self.assertIn('def originalRows : List Nat := [27052, 27053, 179944, 200769]', source)
        self.assertIn('Compiler.unoutline_rows_sound rho 200692 rawRows satisfied constantLink', source)
        self.assertIn('Compiler.checked_product_sound rho rows inverse asset', source)
        self.assertIn('Compiler.checked_assertion_sound rho rows [(0, 1)] product', source)
        self.assertEqual(re.findall(r'#check @(\w+)', source),
                         ['constantLink', 'inverse_equation', 'asset_nonzero',
                          'inverse_square_completion', 'complete_preserves', 'complete_preserves_roles',
                          'complete_satisfies', 'local_completion'])
        signature = source.split('theorem asset_nonzero', 1)[1].split(':= by', 1)[0]
        self.assertIn('(satisfied : Satisfies rho rawRows) : eval rho asset ≠ 0', signature)
        self.assertEqual(signature.count('eval rho asset ≠ 0'), 1)
        self.assertNotRegex(source, r'\b(?:sorry|admit|axiom|native_decide)\b')
        self.assertIn('set_option maxHeartbeats 500000', source)
        self.assertEqual(asset.generate(copy.deepcopy(fixture())), source)

    def test_completion_statement_is_constructive_and_preserves_roles(self):
        source = asset.generate(fixture())
        self.assertIn('def completionWrites : List Nat := [1992, 49790, 49791, 200692]', source)
        self.assertIn('if column = 1992 then (rho 6)⁻¹', source)
        self.assertIn('else if column = 49791 then ((rho 6)⁻¹ - rho 6) ^ 2', source)
        self.assertIn('else rho column', source)
        signature = source.split('theorem local_completion', 1)[1].split(':= by', 1)[0]
        self.assertIn('(one : rho 0 = 1) (nonzero : rho 6 ≠ 0)', signature)
        self.assertIn('∃ completed : Nat → F, Satisfies completed rawRows', signature)
        self.assertIn('column ∉ completionWrites → completed column = rho column', signature)
        for column in (0, 1, 2, 6):
            self.assertIn(f'completed {column} = rho {column}', signature)
        # Legal input premises precede the existential; no inverse/product or
        # satisfying-assignment equation is used as a completion premise.
        premises = signature.split('∃ completed', 1)[0]
        self.assertNotIn('Satisfies', premises)
        self.assertNotIn('eval', premises)
        self.assertNotIn('CharP', signature)
        self.assertIn('No theorem here asserts their preservation.', source)

    def test_local_completion_satisfies_rows_and_changes_only_four_columns(self):
        rows = fixture()['selected_rows']
        for legal_asset in (1, 2, 17, 256, 2**128, asset.P - 1):
            rho = {column: (97 * column + 13) % asset.P for column in range(81)}
            rho.update({0: 1, 6: legal_asset, 1992: 123, 49790: 456, 49791: 789,
                        200692: 321, 262143: 9981})
            original = copy.deepcopy(rho)
            completed = asset.complete_assignment(rho)
            self.assertEqual(rho, original)
            changed = {column for column in completed if completed[column] != original[column]}
            self.assertEqual(changed, {1992, 49790, 49791, 200692})
            for column in set(rho) - {1992, 49790, 49791, 200692}:
                self.assertEqual(completed[column], rho[column])
            for row in rows:
                def evaluate(terms):
                    return sum(completed.get(column, 0) * int(value, 16)
                               for column, value in terms) % asset.P
                self.assertEqual(pow(evaluate(row['a']), 2, asset.P), evaluate(row['b']))
            self.assertEqual(completed[1992] * completed[6] % asset.P, 1)
            self.assertEqual(completed[49790], 1)
            self.assertEqual(completed[200692], 1)

    def test_local_completion_rejects_illegal_inputs_and_does_not_preserve_overlapping_rows(self):
        for rho in ({0: 1, 6: 0}, {0: 0, 6: 17}, {6: 17}, {0: 1},
                    {0: 1, 6: True}, {0: 1, 6: 17, 9: asset.P},
                    {0: 1, 6: 17, -1: 3}, []):
            with self.subTest(rho=rho), self.assertRaises(RelationError):
                asset.complete_assignment(rho)
        rho = {0: 1, 6: 1, 1992: 123}
        completed = asset.complete_assignment(rho)
        # A synthetic unrelated row fixes the inverse to a different value.
        # It holds before the local completion and fails afterwards; only the
        # four selected rows have a completion theorem.
        self.assertEqual(rho[1992] ** 2 % asset.P, 15129 * rho[0])
        self.assertNotEqual(completed[1992] ** 2 % asset.P, 15129 * completed[0])

    def test_semantic_controls_observe_each_single_omission(self):
        extracted = fixture()
        result = asset.omission_controls(extracted)
        self.assertEqual([case['asset'] for case in result['positive']], [1, 17])
        self.assertEqual([case['omitted_row'] for case in result['zero_asset_omissions']],
                         [27052, 27053, 179944, 200769])
        # Independently evaluate serialized equations, including the omitted row.
        def failures(assignment):
            rho = dict(assignment)
            def evaluate(terms):
                return sum(rho[column] * int(value, 16) for column, value in terms) % asset.P
            return [row['row'] for row in extracted['selected_rows']
                    if pow(evaluate(row['a']), 2, asset.P) != evaluate(row['b'])]
        for case in result['positive']:
            self.assertEqual(failures(case['assignment']), [])
            self.assertNotEqual(dict(case['assignment'])[6], 0)
        for case in result['zero_asset_omissions']:
            self.assertEqual(failures(case['assignment']), [case['omitted_row']])
            self.assertEqual(dict(case['assignment'])[6], 0)
            self.assertTrue(case['remaining_selected_rows_satisfied'])
        self.assertEqual(result['constructive_completion']['writes'], [1992, 49790, 49791, 200692])
        for case in result['constructive_completion']['cases']:
            self.assertEqual(failures(case['completed_assignment']), [])
            before, after = dict(case['input_assignment']), dict(case['completed_assignment'])
            self.assertEqual(before[6], after[6])
            self.assertEqual([before[c] for c in (0, 1, 2, 73)], [after[c] for c in (0, 1, 2, 73)])

    def test_identity_and_scope_are_closed(self):
        for key, changed in [('schema', 'unknown'), ('domain_size', 131072),
                             ('stored_rows', True), ('relation_digest', '0' * 64),
                             ('raw_sha256', '0' * 64), ('source_public', [[1, 22735]]),
                             ('source_blocks', [[[1, 7]]])]:
            value = fixture()
            value['identity'][key] = changed
            with self.subTest(key=key), self.assertRaisesRegex(RelationError, 'identity mismatch'):
                asset.generate(value)
        for key, changed in [('schema', 'unknown'), ('scope', 'certified'), ('extra', True)]:
            value = fixture()
            value[key] = changed
            with self.subTest(key=key), self.assertRaisesRegex(RelationError, 'schema/scope'):
                asset.generate(value)
        value = fixture()
        value['identity']['source_public'][0][0] = True
        with self.assertRaisesRegex(RelationError, 'unsigned integer'):
            asset.generate(value)

    def test_changed_rows_refused_before_generating_or_running_controls(self):
        mutations = [lambda rows: rows.pop(),
                     lambda rows: rows.reverse(),
                     lambda rows: rows.append(copy.deepcopy(rows[0])),
                     lambda rows: rows[0].update(row=27051),
                     lambda rows: rows[0]['a'][0].__setitem__(1, f'{1:064x}'),
                     lambda rows: rows[1]['b'][0].__setitem__(1, f'{3:064x}'),
                     lambda rows: rows[2]['a'][1].__setitem__(0, 200691),
                     lambda rows: rows[3]['a'][0].__setitem__(0, 1)]
        for mutate in mutations:
            value = fixture()
            mutate(value['selected_rows'])
            for operation in (asset.generate, asset.omission_controls):
                with self.subTest(mutation=mutate, operation=operation), self.assertRaises(RelationError):
                    operation(value)

    def test_unknown_row_and_noncanonical_term_refused(self):
        for mutate in (lambda row: row.update(extra=True),
                       lambda row: row.update(row=True),
                       lambda row: row['a'].reverse(),
                       lambda row: row['a'][0].__setitem__(1, '0' * 64),
                       lambda row: row['a'][0].__setitem__(1, f'{asset.P:064x}')):
            value = fixture()
            mutate(value['selected_rows'][0])
            with self.assertRaises(RelationError):
                asset.generate(value)

    def test_inspect_delegates_full_stream_and_does_not_swallow_digest_failure(self):
        value = fixture()
        stream = io.BytesIO(b'diagnostic placeholder; mock is not a row qualification')
        def full_inspect(actual_stream, expected, observe):
            self.assertIs(actual_stream, stream)
            self.assertEqual(expected, value['identity']['relation_digest'])
            observe(dict(row=0, a=[], b=[]))
            for row in value['selected_rows']:
                observe(copy.deepcopy(row))
            return copy.deepcopy(value['identity'])
        with patch.object(asset.relation, 'inspect', side_effect=full_inspect) as checked:
            self.assertEqual(asset.inspect(stream), value)
            checked.assert_called_once()
        with patch.object(asset.relation, 'inspect', side_effect=RelationError('exported rows do not match relation digest')):
            with self.assertRaisesRegex(RelationError, 'do not match relation digest'):
                asset.inspect(stream)

    def test_retained_extraction_requires_exact_bytes_and_revalidates_rows(self):
        data = (json.dumps(fixture()) + '\n').encode()
        digest = hashlib.sha256(data).hexdigest()
        self.assertEqual(asset.from_extraction_bytes(data, digest), fixture())
        for altered, expected, reason in ((data, '0' * 64, 'byte identity'),
                                          (data + b' ', digest, 'byte identity'),
                                          (data, None, 'SHA256 required'),
                                          (data, digest.upper(), 'SHA256 required')):
            with self.subTest(reason=reason), self.assertRaisesRegex(RelationError, reason):
                asset.from_extraction_bytes(altered, expected)
        changed = fixture()
        changed['selected_rows'][1]['b'][0][1] = f'{3:064x}'
        bad = (json.dumps(changed) + '\n').encode()
        with self.assertRaisesRegex(RelationError, 'exact row/operand'):
            asset.from_extraction_bytes(bad, hashlib.sha256(bad).hexdigest())
        duplicate = b'{"schema":"unknown","schema":"unknown"}\n'
        with self.assertRaisesRegex(RelationError, 'duplicate JSON key'):
            asset.from_extraction_bytes(duplicate, hashlib.sha256(duplicate).hexdigest())

    def test_cli_retained_extraction_mode_records_identity_without_stream_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            data = (json.dumps(fixture()) + '\n').encode()
            (base / 'accepted-extraction.json').write_bytes(data)
            digest = hashlib.sha256(data).hexdigest()
            argv = ['asset', '--extracted', str(base / 'accepted-extraction.json'),
                    '--expected-extraction-sha256', digest, '--output-dir', str(base / 'candidate')]
            with patch.object(sys, 'argv', argv), patch.object(asset, 'inspect') as checked, \
                 patch('sys.stdout', new=io.StringIO()):
                asset.main()
            checked.assert_not_called()
            manifest = json.loads((base / 'candidate/manifest.json').read_text())
            self.assertEqual(manifest['generation_input']['sha256'], digest)
            self.assertIn('prior whole-stream receipt required', manifest['generation_input']['kind'])
            self.assertEqual(manifest['completion_writes'], [1992, 49790, 49791, 200692])
            self.assertIn('other Transfer rows may change', manifest['completion_scope'])
            source = (base / 'candidate/RuntimeTransferAssetNonzero.lean').read_bytes()
            self.assertEqual(manifest['generated_sha256'], hashlib.sha256(source).hexdigest())

    def test_existing_packet_refused_without_reading_stream(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(sys, 'argv', ['asset', '--relation', 'unused', '--output-dir', directory]), \
                 patch.object(asset, 'inspect') as checked, patch('sys.stderr', new=io.StringIO()):
                with self.assertRaises(SystemExit) as exited:
                    asset.main()
            self.assertEqual(exited.exception.code, 2)
            checked.assert_not_called()
            self.assertEqual(list(Path(directory).iterdir()), [])


if __name__ == '__main__':
    unittest.main()
