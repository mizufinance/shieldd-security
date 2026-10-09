"""Synthetic row substitution controls; no runtime/kernel certificate."""
import unittest
from circuits import transfer_linear_substitution as substitution
from circuits.transfer_relation import MODULUS, RelationError


class LinearSubstitutionTests(unittest.TestCase):
    def fixture(self):
        source = {0: (((0, 1), (901, -1)), ()), 1: (((10, 1),), ((11, 1),))}
        actual = {4: (((0, 1), (902, -1)), ()), 5: (((30, 1), (31, 1)), ((50, 1),))}
        pairs = [(((10, 1),), ((30, 1), (31, 1))), (((11, 1),), ((50, 1),))]
        return source, actual, pairs

    def infer(self, source, actual, pairs, row_pairs=None):
        return substitution.infer(pairs, [(0, 4), (1, 5)] if row_pairs is None else row_pairs,
                                  source, actual, source_copy=901, actual_copy=902)

    def test_multiterm_image_transports_an_actual_satisfying_assignment(self):
        source, actual, pairs = self.fixture()
        accepted = self.infer(source, actual, pairs)
        columns = dict(accepted['columns'])
        self.assertEqual(columns[10], ((30, 1), (31, 1)))
        rho = {0: 1, 902: 1, 30: 2, 31: 3, 50: 25}
        evaluate = lambda terms: sum(factor * rho.get(column, 0) for column, factor in terms) % MODULUS
        sigma = {column: evaluate(terms) for column, terms in columns.items()}
        for row in actual.values():
            self.assertEqual(evaluate(row[0]) ** 2 % MODULUS, evaluate(row[1]))
        for row in source.values():
            value = lambda terms: sum(factor * sigma[column] for column, factor in terms) % MODULUS
            self.assertEqual(value(row[0]) ** 2 % MODULUS, value(row[1]))
        self.assertEqual(sigma[10], 5)

    def test_scalar_coefficients_and_negated_square_inputs(self):
        source, actual, pairs = self.fixture()
        source[1] = (((10, 2),), ((11, 1),))
        actual[5] = (((30, -3),), ((50, 1),))
        pairs[0] = (((10, 2),), ((30, 3),))
        accepted = self.infer(source, actual, pairs)
        self.assertEqual(dict(accepted['columns'])[10], ((30, 3 * pow(2, -1, MODULUS) % MODULUS),))

    def test_rehashed_role_row_and_coverage_changes_refused(self):
        for edit in ('role', 'row', 'missing', 'conflict', 'unknown'):
            source, actual, pairs = self.fixture()
            row_pairs = [(0, 4), (1, 5)]
            if edit == 'role': pairs.append((((10, 1),), ((30, 1),)))
            elif edit == 'row': actual[5] = (((30, 1), (31, 1)), ((51, 1),))
            elif edit == 'missing': row_pairs.pop()
            elif edit == 'conflict': row_pairs.append((1, 4))
            else: source[1] = (((12, 1),), ((11, 1),))
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                self.infer(source, actual, pairs, row_pairs)

    def test_ambiguous_unknowns_and_constant_rebinding_refused(self):
        source, actual, pairs = self.fixture()
        pairs[0] = (((10, 1), (12, 1)), ((30, 1), (31, 1)))
        with self.assertRaisesRegex(RelationError, 'ambiguous'):
            self.infer(source, actual, pairs)
        source, actual, pairs = self.fixture()
        pairs.append((((0, 1),), ((31, 1),)))
        with self.assertRaisesRegex(RelationError, 'role equality'):
            self.infer(source, actual, pairs)
