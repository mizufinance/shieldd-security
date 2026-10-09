import unittest
from unittest.mock import patch

from circuits import generate_transfer_ivk_native_consumer as consumer
from circuits import transfer_relation as relation


class NativeConsumerTests(unittest.TestCase):
    def test_constructed_consumer_and_returned_scalar_reader(self):
        plan = dict(phases=[dict(value=[(1994, 1)], start=1996),
                            dict(value=[(1995, 1)], start=2000)],
                    checked=dict(metadata=dict(constant_copy=200692)))
        with patch.object(consumer.keys, 'generate', return_value=('validated', 'source')) as strict, \
                patch.object(consumer.keys.native.hashes.ivk, 'inspect_metadata', return_value={}), \
                patch.object(consumer.keys.native.reduction, 'plan', return_value=plan):
            name, source = consumer.generate(b'ivk', {}, b'reduction', {}, 'params', '0'*64, [])
        strict.assert_called_once_with(b'ivk', {}, b'reduction', {}, 'params', '0'*64, [])
        self.assertEqual(name, 'RuntimeTransferIvkNativeConsumerOwned')
        self.assertEqual(source.count('#check @'), 4)
        self.assertEqual(source.count('#print axioms'), 4)
        self.assertIn('ScalarReductionSupport.hash_preserved', source)
        self.assertIn('RuntimeTransferIvkInverseOwnedCompletion.fresh', source)
        self.assertIn('RuntimeTransferIvkHashReductionJoin.hash_value', source)
        self.assertIn('ShielddViewingKeyScalar.scalar_value', source)
        self.assertIn('GroupNativeSdk.scalar_read', source)
        self.assertIn('TransferReduction.decode_canonical_cast', source)
        for export in ('constructed_consumer', 'native_consumer_value',
                       'native_consumer_integer', 'native_reader_consumer'):
            statement = source.split('theorem '+export, 1)[1].split(' := by', 1)[0]
            self.assertNotIn('Satisfies', statement)
            self.assertNotIn('desired', statement)
            self.assertNotIn('hashMeaning', statement)
        self.assertIn('incomingScalar primitives', source)
        self.assertIn('ShielddNativeIvkSdkProgram.ivk fq', source)

    def test_strict_actual_roles_are_mandatory(self):
        with patch.object(consumer.keys, 'generate', side_effect=relation.RelationError('role mismatch')), \
                patch.object(consumer.keys.native.hashes.ivk, 'inspect_metadata') as metadata:
            with self.assertRaises(relation.RelationError):
                consumer.generate(b'ivk', {}, b'reduction', {}, 'params', '0'*64)
        metadata.assert_not_called()


if __name__ == '__main__':
    unittest.main()
