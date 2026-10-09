"""Small source-helper checks; these provide no all-row/kernel proof credit."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'circuits'))
import compiler_completion as completion


class CompilerCompletionBoundaryTests(unittest.TestCase):
    def test_retired_or_selected_row_count_is_refused(self):
        for size in (8636, 201396):
            with self.subTest(size=size), self.assertRaisesRegex(ValueError, '200770-row'):
                completion.select([None] * size, [], [0, 1, 2, 200692], 200692)

    def test_pinned_copy_role_is_required(self):
        with self.assertRaisesRegex(ValueError, 'constant-copy column 200692'):
            completion.select([None] * completion.STORED_ROWS, [], [0, 1, 2, 42], 42)

    def test_public_and_committed_columns_must_be_preserved(self):
        for kept in ([0, 2, 200692], [0, 1, 200692], [0, 1, 2, 200692, 2]):
            with self.subTest(kept=kept), self.assertRaisesRegex(ValueError, 'preserved constant/public/committed'):
                completion.select([None] * completion.STORED_ROWS, [], kept, 200692)

    def test_product_uses_two_actual_rows_and_retains_fused_remainder(self):
        expected, writes, reads, _ = completion._step({
            'kind': 'product', 'source_kind': 'node', 'source_id': 1,
            'row_indices': [0, 1], 'left': [(3, 1)], 'right': [(4, 1)],
            'remainder': [(5, 2)], 'output': 6, 'auxiliary': 7})
        self.assertEqual(writes, [6, 7])
        self.assertEqual(reads, ((3, 1), (4, 1), (5, 2)))
        self.assertEqual(expected, [(((3, 1), (4,
            52435875175126190479447740508185965837690552500527637822603658699938581184512)), ((7, 1),)),
            (((3, 1), (4, 1)), ((5, 8), (6, 4), (7, 1)))])

    def test_materialization_cannot_read_its_output(self):
        with self.assertRaisesRegex(ValueError, 'pivot occurs in its own operands'):
            completion._step({'kind': 'square', 'source_kind': 'node', 'source_id': 2,
                'row_indices': [0], 'input': [(3, 1)], 'remainder': [(6, 2)], 'output': 6})


if __name__ == '__main__':
    unittest.main()
