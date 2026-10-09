"""Synthetic real-row Boolean boundary; no actual regulated caller claim."""
import unittest
from circuits import generate_transfer_encryption_dh_regulated_boolean as renderer
from circuits.transfer_relation import RelationError
from tests.test_transfer_encryption_dh_keys import fixture as keys
from tests.test_transfer_encryption_dh_boolean_renderer import fixture as rows


class EncryptionDhRegulatedBooleanTests(unittest.TestCase):
    def fixture(self):
        checked = keys()
        original, extracted = rows()
        checked['metadata'] = original['metadata']
        return checked, extracted

    def test_booleanity_follows_from_actual_input_row_without_branch_premise(self):
        checked, extracted = self.fixture()
        name, text = renderer.generate(checked, extracted)
        self.assertEqual(name, 'RuntimeTransferEncryptionRegulatedFlag')
        self.assertIn('originalRows : List Nat := [10, 11]', text)
        self.assertIn('EncryptionDhBoolean.asserted', text)
        self.assertIn('def value0 : Linear := [(3, (1 : Int))]', text)
        signature = text.split('theorem flag_boolean', 1)[1].split(':= by', 1)[0]
        self.assertIn('satisfied : Satisfies rho rawRows', signature)
        self.assertNotIn('(boolean', signature)
        self.assertNotIn('regulator', signature)

    def test_changed_boolean_row_missing_input_or_wrong_role_are_refused(self):
        for change in ('row', 'missing', 'role', 'pending'):
            checked, extracted = self.fixture()
            if change == 'row': extracted['selected_rows'][1]['b'][0][1] = f'{2:064x}'
            elif change == 'missing': extracted['selected_rows'].pop(1)
            elif change == 'role': checked['metadata']['role'] = 1
            else: checked['qualified'] = False
            with self.subTest(change=change), self.assertRaises(RelationError):
                renderer.generate(checked, extracted)
