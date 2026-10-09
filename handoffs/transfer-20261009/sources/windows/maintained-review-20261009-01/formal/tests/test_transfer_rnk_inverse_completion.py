"""Typed inverse-footprint fixtures; no runtime or proof qualification."""
import json
import re
import unittest
from unittest.mock import patch

from circuits import transfer_rnk_inverse_completion as inverse
from circuits import generate_transfer_rnk_inverse_completion as generator
from circuits.transfer_relation import RelationError
from tests import test_generate_transfer_rnk_sparse_sequence as fixtures
from tests.test_transfer_rnk_completion import row


class RnkInverseFootprintTests(unittest.TestCase):
    def fixture(self):
        sequence = fixtures.SyntheticRnkSequenceRendererTests().fixture()
        identity = dict(relation_digest='a'*64, domain_size=262144, stored_rows=200770)
        sequence['identity'] = identity
        sequence['observed_output'] = [[(3763, 1)], [(3764, 1)]]
        checked = dict(metadata=dict(relation_digest=identity['relation_digest'],
            domain_size=262144, full_rows=200770, constant_copy=200692),
            derived={1: ((3763, 1),), 2: ((3764, 1),), 3: ((3765, 1),)},
            points=dict(output=[('source', 1), ('source', 2)]),
            nonidentity_inverse=('source', 3))
        rows = [row(38038, [(3763, -1), (3765, 1)], [(60777, 1)]),
            row(38039, [(3763, 1), (3765, 1)], [(60776, 4), (60777, 1)]),
            row(181725, [(60776, -1), (200692, 1)], []),
            row(200769, [(0, 1), (200692, -1)], [])]
        extracted = dict(identity=identity, selected_rows=rows,
            products=[dict(role='nonidentity', rows=[38038, 38039, 181725])])
        return checked, extracted, sequence

    def selected(self, *values):
        # Isolate this additive footprint consumer's checks. The production
        # path invokes the existing strict accepted-row validator first.
        with patch.object(inverse.owner, 'generate_rnk_inverse_boundary', return_value=''):
            return inverse.plan(*values)

    def test_exact_three_writes_and_json_roundtrip(self):
        checked, extracted, sequence = self.fixture()
        result = self.selected(checked, extracted, sequence)
        self.assertEqual(result['writes'], [3765, 60776, 60777])
        self.assertEqual([value['row'] for value in result['rows']], [38038, 38039, 181725, 200769])
        self.assertEqual(result, self.selected(checked, json.loads(json.dumps(extracted)),
            json.loads(json.dumps(sequence))))

    def test_whole_window_certificate_and_identity_refusal(self):
        checked, extracted, sequence = self.fixture()
        sequence['target_writes'].append(3765)
        with self.assertRaises(RelationError): self.selected(checked, extracted, sequence)
        checked, extracted, sequence = self.fixture()
        extracted['identity'] = {**extracted['identity'], 'stored_rows': 200769}
        with self.assertRaises(RelationError): self.selected(checked, extracted, sequence)

    def test_protected_consumer_and_observed_output_refusal(self):
        checked, extracted, sequence = self.fixture()
        sequence['protected_columns'].append(60776)
        with self.assertRaises(RelationError): self.selected(checked, extracted, sequence)
        checked, extracted, sequence = self.fixture()
        sequence['observed_output'][0][0] = (3762, 1)
        with self.assertRaises(RelationError): self.selected(checked, extracted, sequence)

    def test_actual_row_validator_is_required_and_typed_fail_closed(self):
        values = self.fixture()
        with patch.object(inverse.owner, 'generate_rnk_inverse_boundary',
                          side_effect=RelationError('strict original row mismatch')):
            with self.assertRaises(RelationError): inverse.plan(*values)
        checked, extracted, sequence = self.fixture()
        del extracted['products']
        with self.assertRaises(RelationError): self.selected(checked, extracted, sequence)

    def test_two_finite_modules_no_desired_truth_or_output_premise(self):
        checked, extracted, sequence = self.fixture()
        with patch.object(inverse.owner, 'generate_rnk_inverse_boundary', return_value=''):
            modules = generator.generate(checked, extracted, sequence)
        self.assertEqual(set(modules), {'RuntimeRnkInverseFootprint', 'RuntimeRnkNativeInverseCompletion'})
        count = 0
        for source in modules.values():
            checks = re.findall(r'^#check @([^\s]+)', source, re.M)
            prints = re.findall(r'^#print axioms ([^\s]+)', source, re.M)
            self.assertEqual(checks, prints)
            count += len(checks)
            self.assertNotRegex(source, r'\((?:satisfied|constructed|desired)\s*:')
            self.assertNotRegex(source, r'\b(?:sorry|admit|native_decide|axiom)\b')
        self.assertEqual(count, 5)
        leaf = modules['RuntimeRnkNativeInverseCompletion']
        self.assertIn('ShielddViewingKeyAdmission.successful_scalar', leaf)
        self.assertIn('GroupNativeSubgroupMultiply.canonical_input_multiple_inverse', leaf)
        self.assertIn('RuntimeRnkNativeCompletion.actual_rows_complete', leaf)
        self.assertIn('Scalar.order • upstream.embed', leaf)


if __name__ == '__main__': unittest.main()
