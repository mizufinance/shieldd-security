"""Typed synthetic role/LC controls; no actual runtime or kernel credit."""
import copy
import re
import unittest
from circuits import generate_transfer_encryption_dh_admission as renderer
from circuits.transfer_relation import RelationError
from tests.test_transfer_encryption_dh_selection_renderer import fixture


class DhAdmissionSourceTests(unittest.TestCase):
    def test_all_roles_discharge_base_and_key_endpoint_premises(self):
        first, _ = fixture(0)
        for role in range(5):
            checked, _ = fixture(role)
            name, text = renderer.generate(first, checked)
            self.assertEqual(name, f'RuntimeTransferEncryptionDh{role}Admission')
            checks = re.findall(r'^#check @([\w.]+)$', text, re.M)
            self.assertEqual(len(checks), 4)
            self.assertEqual(checks, re.findall(r'^#print axioms ([\w.]+)$', text, re.M))
            self.assertIn('RuntimeTransferEncryptionKeyAdmission.represented_selected_keys', text)
            self.assertIn('RuntimeTransferSpendAuthGenerator.base_meaning', text)
            self.assertIn('standardPrime baseOrder baseNonzero', text)
            signature = text.split('theorem native_admitted', 1)[1].split(':= by', 1)[0]
            self.assertNotIn('(baseRole :', signature)
            self.assertNotIn('(baseMeaning :', signature)
            self.assertNotIn('(subgroup :', signature)
            self.assertNotIn('(nonidentity :', signature)
            self.assertIn('(meaningSatisfied :', signature)
            self.assertIn('(detectionSatisfied :', signature)
            self.assertIn('(payloadSatisfied :', signature)
            self.assertNotRegex(text, r'\b(sorry|admit|axiom|native_decide)\b')
            if role:
                self.assertIn(f'RuntimeTransferEncryptionDh{role}Flag.flag_boolean', text)
                self.assertIn(f'RuntimeTransferEncryptionDh{role}Selection.axis0_interpolation', text)
            else:
                self.assertNotIn('(flagSatisfied :', signature)
                self.assertIn('RuntimeTransferEncryptionKeyMeaning.selectedDetection rho := rfl', text)

    def test_foreign_capture_selected_lc_or_source_cannot_replace_actual_base(self):
        first, _ = fixture(0)
        for change in ('pending', 'schema', 'bool_role', 'identity', 'foreign_key', 'base_source'):
            checked, _ = fixture(2)
            if change == 'pending':
                checked['qualified'] = False
            elif change == 'schema':
                checked['metadata']['schema'] = 'shieldd-transfer-ownership-v1'
            elif change == 'bool_role':
                checked['metadata']['role'] = True
            elif change == 'identity':
                checked['metadata']['relation_digest'] = 'c'*64
            elif change == 'foreign_key':
                observed = checked['bindings']['detection_key'][0][1]
                checked['derived'][observed] = ((999, 1),)
            else:
                checked['points']['base'] = checked['bindings']['payload_key']
            with self.subTest(change=change), self.assertRaises(RelationError):
                renderer.generate(first, checked)

    def test_first_key_admission_role_is_required(self):
        checked, _ = fixture(1)
        for role in (1, True):
            first, _ = fixture(0)
            first['metadata']['role'] = role
            with self.assertRaises(RelationError):
                renderer.generate(first, checked)


if __name__ == '__main__':
    unittest.main()
