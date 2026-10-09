"""Flat H kept-list regression; mocked renderer input grants no proof credit."""
import unittest
from unittest.mock import patch

from circuits import generate_transfer_balance_blinding_template_canonical_ingress_current as current
from circuits.transfer_relation import RelationError
from tests import test_generate_transfer_balance_blinding_template_composition as fixtures


class CurrentBlindingIngressTests(unittest.TestCase):
    def fixture(self):
        return fixtures.BlindingTemplateCompositionTests().fixture()

    def test_only_aggregate_membership_proofs_change(self):
        with patch.object(current.original.whole, 'plan', return_value=self.fixture()):
            old = current.original.generate_modules(None, [], [], [], {}, 0)
            new = current.generate_modules(None, [], [], [], {}, 0)
        self.assertEqual(old[0], new[0])
        self.assertEqual(old[1][0], new[1][0])
        self.assertNotIn('keptPart', new[1][1])
        self.assertIn('ingress.2.2.2 0 (by decide)', new[1][1])
        self.assertIn('ingress.2.2.2 200692 (by decide)', new[1][1])
        self.assertEqual(new[1][1].count('#check @'), 2)

    def test_other_pages_are_exactly_unchanged(self):
        with patch.object(current.original.whole, 'plan', return_value=self.fixture()):
            for page in range(1, 8):
                self.assertEqual(current.original.generate_modules(None, [], [], [], {}, page),
                                 current.generate_modules(None, [], [], [], {}, page))

    def test_genuine_allocation_refusal_is_preserved(self):
        fixture = self.fixture()
        fixture['canonical']['value'] += 1
        with patch.object(current.original.whole, 'plan', return_value=fixture):
            with self.assertRaises(RelationError):
                current.generate_modules(None, [], [], [], {}, 0)
