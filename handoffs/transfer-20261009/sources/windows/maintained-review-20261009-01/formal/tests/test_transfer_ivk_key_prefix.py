import unittest
from unittest.mock import patch

from circuits import generate_transfer_ivk_key_prefix as keys
from circuits import transfer_relation as relation


class KeyPrefixTests(unittest.TestCase):
    def test_constructed_inputs_and_defined_decoded_ak_path(self):
        with patch.object(keys.native, 'generate', return_value=('validated', 'source')) as validated, \
                patch.object(keys.native.hashes.ivk, 'inspect_metadata',
                             return_value=dict(metadata=dict(constant_copy=200692))):
            name, source = keys.generate(b'ivk', {}, b'reduction', {}, 'params', '0'*64, [])
        validated.assert_called_once_with(b'ivk', {}, b'reduction', {}, 'params', '0'*64, [])
        self.assertEqual(name, 'RuntimeTransferIvkKeyPrefixOwned')
        self.assertEqual(source.count('#check @'), 3)
        self.assertEqual(source.count('#print axioms'), 3)
        self.assertIn('RuntimeTransferIvkHashReductionJoin.inputs_preserved', source)
        self.assertIn('RuntimeTransferIvkInverseOwnedCompletion.preserves', source)
        self.assertIn('ShielddViewingKeyCoordinates.seeded_key_coordinates', source)
        self.assertIn('ShielddNativeIvkSdkProgram.ivk_value', source)
        self.assertIn('ShielddViewingKeyAdmission.accepted_field_legal', source)
        self.assertIn('upstream.decodePoint (upstream.keyBytes key) = some point', source)
        for theorem in ('key_coordinates', 'original_rows_complete'):
            statement = source.split('theorem '+theorem, 1)[1].split(' :=', 1)[0]
            self.assertNotIn('Satisfies base', statement)
            self.assertNotIn('coordinateMeaning', statement)
            self.assertNotIn('eval base', statement)
        statement = source.split('theorem original_rows_complete', 1)[1].split(' := by', 1)[0]
        self.assertIn('ShielddNativeIvkSdkProgram.ivk fq', statement)
        self.assertNotIn('ShielddNativeIvkSource.sdkIvk', statement)

    def test_strict_native_singleton_ingress_cannot_be_skipped(self):
        with patch.object(keys.native, 'generate', side_effect=relation.RelationError('role mismatch')), \
                patch.object(keys.native.hashes.ivk, 'inspect_metadata') as checked:
            with self.assertRaises(relation.RelationError):
                keys.generate(b'ivk', {}, b'reduction', {}, 'params', '0'*64)
        checked.assert_not_called()


if __name__ == '__main__':
    unittest.main()
