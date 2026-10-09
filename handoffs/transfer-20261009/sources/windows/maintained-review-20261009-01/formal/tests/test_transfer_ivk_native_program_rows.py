import unittest
from unittest.mock import patch
from circuits import generate_transfer_ivk_native_program_rows as generator
from circuits.transfer_relation import RelationError


class NativeProgramRowsTests(unittest.TestCase):
    def test_same_accepted_sdk_scalar_constructs_original_rows(self):
        native=generator.values.bits.consumer.keys.native
        with patch.object(generator.values,'generate',return_value=('validated','source')), \
             patch.object(native.hashes.ivk,'inspect_metadata',return_value={}), \
             patch.object(native.reduction,'plan',return_value=dict(checked=dict(metadata=dict(constant_copy=200692)))):
            name,source=generator.generate(b'ivk',{},b'reduction',{},'params','a'*64)
        self.assertEqual(name,'RuntimeTransferIvkNativeProgramRows')
        self.assertEqual(source.count('#check @'),1)
        self.assertEqual(source.count('#print axioms'),1)
        self.assertIn('ShielddViewingKeyScalar.scalar_integer',source)
        self.assertIn('ShielddViewingKeyAdmission.successful_scalar',source)
        self.assertIn('RuntimeTransferIvkInversePrefixJoin.original_complete',source)
        statement=source.split('theorem original_rows_complete',1)[1].split(' := by',1)[0]
        premises=statement.split(' :\n',1)[0]
        self.assertNotIn('Satisfies',premises)
        self.assertNotIn('denominator',premises)
        self.assertNotIn('legalInput',premises)
        self.assertIn('ShielddNativeIvkSdkProgram.ivk',premises)
        self.assertNotIn('ShielddNativeIvkSource.sdkIvk',premises)

    def test_typed_native_parent_refusal_propagates(self):
        with patch.object(generator.values,'generate',side_effect=RelationError('role mismatch')):
            with self.assertRaises(RelationError):
                generator.generate(b'ivk',{},b'reduction',{},'params','a'*64)


if __name__=='__main__':unittest.main()
