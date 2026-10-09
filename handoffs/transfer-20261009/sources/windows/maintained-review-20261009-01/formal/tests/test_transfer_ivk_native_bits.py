import unittest
from unittest.mock import patch

from circuits import generate_transfer_ivk_native_bits as bits
from circuits import transfer_relation as relation


class NativeBitsTests(unittest.TestCase):
    def render(self, plan):
        with patch.object(bits.consumer, 'generate', return_value=('validated', 'source')), \
                patch.object(bits.consumer.keys.native.hashes.ivk, 'inspect_metadata', return_value={}), \
                patch.object(bits.consumer.keys.native.reduction, 'plan', return_value=plan):
            return bits.generate(b'ivk', {}, b'reduction', {}, 'params', '0'*64)

    def plan(self):
        return dict(phases=[dict(value=[(1994, 1)], start=1996),
                            dict(value=[(1995, 1)], start=2000, width=252,
                                 columns=list(range(2000, 2252)))],
                    checked=dict(metadata=dict(constant_copy=200692)))

    def test_exact_written_boolean_list_and_returned_scalar(self):
        name, source = self.render(self.plan())
        self.assertEqual(name, 'RuntimeTransferIvkNativeBitsOwned')
        self.assertEqual(source.count('#check @'), 3)
        self.assertEqual(source.count('#print axioms'), 3)
        self.assertIn('ScalarConstructedBits.decoded_singletons', source)
        self.assertIn('writeBits_map', source)
        self.assertIn('ScalarReductionSupport.written_remainder_bits', source)
        self.assertIn('RuntimeTransferIvkNativeConsumerOwned.native_consumer_integer', source)
        self.assertIn('List.range\' 2000 252', source)
        statement = source.split('theorem native_bits', 1)[1].split(' := by', 1)[0]
        self.assertNotIn('Satisfies', statement)
        self.assertNotIn('bitMeaning', statement)
        self.assertNotIn('reconstruction', statement)
        self.assertIn('encodeBits 252 (fr.integer scalar)', statement)
        self.assertIn('GroupByteCodec.canonical_reader_join', source)
        reader = source.split('theorem native_reader_bits', 1)[1].split(' := by', 1)[0]
        self.assertNotIn('Satisfies', reader)
        self.assertNotIn('reconstruction', reader)
        self.assertNotIn('accepted', reader)

    def test_bit_order_and_width_refuse(self):
        for mutation in ('order', 'width'):
            plan = self.plan()
            if mutation == 'order':
                plan['phases'][1]['columns'][0:2] = [2001, 2000]
            else:
                plan['phases'][1]['width'] = 255
            with self.assertRaises(relation.RelationError):
                self.render(plan)

    def test_native_ingress_refusal_propagates(self):
        with patch.object(bits.consumer, 'generate', side_effect=relation.RelationError('role mismatch')), \
                patch.object(bits.consumer.keys.native.hashes.ivk, 'inspect_metadata') as metadata:
            with self.assertRaises(relation.RelationError):
                bits.generate(b'ivk', {}, b'reduction', {}, 'params', '0'*64)
        metadata.assert_not_called()


if __name__ == '__main__':
    unittest.main()
