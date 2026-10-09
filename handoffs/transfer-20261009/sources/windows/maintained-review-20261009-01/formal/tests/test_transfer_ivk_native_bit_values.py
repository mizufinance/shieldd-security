import unittest
from unittest.mock import patch
from circuits import generate_transfer_ivk_native_bit_values as generator
from circuits.transfer_relation import RelationError


class NativeBitValuesTests(unittest.TestCase):
    def plan(self):
        return dict(phases=[dict(value=[(1994,1)],start=1996),
            dict(value=[(1995,1)],start=2000,width=252,columns=list(range(2000,2252)))],
            checked=dict(metadata=dict(constant_copy=200692)))

    def render(self,plan):
        with patch.object(generator.bits,'generate',return_value=('validated','source')), \
             patch.object(generator.bits.consumer.keys.native.hashes.ivk,'inspect_metadata',return_value={}), \
             patch.object(generator.bits.consumer.keys.native.reduction,'plan',return_value=plan):
            return generator.generate(b'ivk',{},b'reduction',{},'params','a'*64)

    def test_field_values_are_written_then_native_list_joined(self):
        name,source=self.render(self.plan())
        self.assertEqual(name,'RuntimeTransferIvkNativeBitValuesOwned')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertIn('ScalarWrittenBitValues.preserved_bit_value',source)
        self.assertIn('ScalarReductionSupport.written_remainder_bits',source)
        self.assertIn('RuntimeTransferIvkNativeBitsOwned.native_bits',source)
        self.assertIn('RuntimeTransferIvkInversePrefixJoin.completed codec base (2000+index)',source)
        statement=source.split('theorem native_values',1)[1].split(' := by',1)[0]
        for forbidden in ('Satisfies','reconstruction','bitMeaning','OnCurve'):
            self.assertNotIn(forbidden,statement)
        self.assertIn('some scalar',statement)

    def test_order_width_and_native_ingress_fail_closed(self):
        for mutation in ('order','width'):
            plan=self.plan()
            if mutation=='order':plan['phases'][1]['columns'][0:2]=[2001,2000]
            else:plan['phases'][1]['width']=255
            with self.assertRaises(RelationError):self.render(plan)
        with patch.object(generator.bits,'generate',side_effect=RelationError('native acceptance')):
            with self.assertRaises(RelationError):
                generator.generate(b'ivk',{},b'reduction',{},'params','a'*64)


if __name__=='__main__':unittest.main()
