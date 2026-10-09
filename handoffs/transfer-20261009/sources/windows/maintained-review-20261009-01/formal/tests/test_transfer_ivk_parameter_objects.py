import unittest
from unittest.mock import patch

from circuits import generate_transfer_ivk_parameter_objects as objects
from circuits import transfer_relation as relation


class ParameterObjectTests(unittest.TestCase):
    def test_object_equality_derived_from_same_canonical_buffers(self):
        with patch.object(objects.readers, 'generate', return_value=('checked', 'source')) as checked:
            name, source = objects.generate(b'ivk', {}, 'params', '0'*64)
        checked.assert_called_once_with(b'ivk', {}, 'params', '0'*64, ())
        self.assertEqual(name, 'RuntimeTransferIvkParameterObjects')
        self.assertEqual(source.count('#check @'), 2)
        self.assertEqual(source.count('#print axioms'), 2)
        self.assertIn('ShielddNativeParameterCodec.circuit_load_cast', source)
        self.assertIn('ShielddNativeParameterCodec.sdk_load_cast', source)
        self.assertIn('RuntimeTransferIvkParameterReaders.sdk_loaded', source)
        for theorem in ('circuit_objects', 'sdk_objects'):
            statement = source.split('theorem '+theorem, 1)[1].split(' := by', 1)[0]
            self.assertNotIn('same :', statement)
            self.assertNotIn('injective', statement)
            self.assertNotIn('canonical :', statement)

    def test_accepted_artifact_check_is_mandatory(self):
        with patch.object(objects.readers, 'generate', side_effect=relation.RelationError('table mismatch')):
            with self.assertRaises(relation.RelationError):
                objects.generate(b'ivk', {}, 'params', '0'*64)


if __name__ == '__main__':
    unittest.main()
