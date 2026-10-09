import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_native_prefix as generator
from circuits.transfer_relation import RelationError


class NativePrefixTests(unittest.TestCase):
    def test_same_scalar_constructs_prefix_and_preserves_it_through_actual_windows(self):
        with patch.object(generator.native,'generate',return_value=('validated','source')), \
             patch.object(generator.frames,'generate',return_value=[]), \
             patch.object(generator.program_rows,'generate',return_value=('validated','source')):
            name,source=generator.generate([dict(metadata=dict(constant_copy=200692))],[{}],
                b'ivk',{},b'reduction',{},'params','a'*64)
        self.assertEqual(name,'RuntimeOwnershipNativePrefix')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertIn('RuntimeTransferIvkNativeProgramRows.original_rows_complete',source)
        self.assertIn('RuntimeOwnershipWindow000PrecomputeFrame.rows_preserved',source)
        self.assertIn('GroupCircuitPrefixTransport.certified_preserves',source)
        self.assertIn('RuntimeOwnershipIvkPrefixFrame.covered',source)
        self.assertIn('RuntimeOwnershipNativeConstructor.native_windows_complete',source)
        premises=source.split('variable (accepted',1)[1].split('include arithmetic',1)[0]
        self.assertIn('ShielddNativeIvkSdkProgram.ivk',premises)
        self.assertNotIn('Satisfies',premises)
        self.assertNotIn('OnCurve',premises)
        self.assertNotIn('senderMeaning',premises)
        self.assertNotIn('namespace G :=',source)

    def test_refuses_unjoined_actual_native_constructor(self):
        with patch.object(generator.native,'generate',side_effect=RelationError('actual bit/source mismatch')):
            with self.assertRaises(RelationError):generator.generate([],[],b'',{},b'',{},'params','a'*64)


if __name__=='__main__':unittest.main()
