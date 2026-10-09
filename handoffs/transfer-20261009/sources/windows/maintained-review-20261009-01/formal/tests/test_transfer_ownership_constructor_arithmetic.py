import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_constructor_arithmetic as generator
from circuits.transfer_relation import RelationError


class ConstructorArithmeticTests(unittest.TestCase):
    def test_actual_bounded_trace_uses_constructed_window_and_owned_bit_rows(self):
        checked=dict(bits=list(range(252)),derived={i:((2000+i,1),) for i in range(252)})
        with patch.object(generator.bits,'generate',return_value=('checked','source')), \
             patch.object(generator.bits.candidates,'_chunk',return_value=(112,14)), \
             patch.object(generator.completion.owner,'generate_trace_chunk',return_value='checked source'):
            name,source=generator.generate(checked,{})
        self.assertEqual(name,'RuntimeOwnershipConstructorArithmetic112')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertEqual(source.count('apply ScalarBitFieldSemantics.field_square'),28)
        self.assertIn('RuntimeOwnershipConstructorChunk112.originalRows',source)
        self.assertIn('RuntimeOwnershipTrace112.actual_trace_equations',source)
        self.assertNotIn('endpointRows',source)
        self.assertNotIn('target_role',source)
        self.assertIn('List.not_mem_nil,or_false',source)
        self.assertIn('using written 0 (by decide)',source)
        self.assertIn('using written 27 (by decide)',source)

    def test_unaccepted_source_bits_refuse(self):
        with patch.object(generator.bits,'generate',side_effect=RelationError('bit row/source mismatch')):
            with self.assertRaises(RelationError):generator.generate({}, {})


if __name__=='__main__':unittest.main()
