import unittest
from unittest.mock import patch
from tests.test_transfer_ownership_constructor_chunk import fixture
from circuits import generate_transfer_ownership_constructor_bits as generator
from circuits.transfer_relation import RelationError


class ConstructorBitsTests(unittest.TestCase):
    def render(self,values):
        checked,selected,plans=values
        with patch.object(generator.completion,'window_plan',side_effect=plans):
            return generator.generate(checked,selected)

    def test_actual_indices_bind_field_values_without_boolean_assumption(self):
        name,source=self.render(fixture(2))
        self.assertEqual(name,'RuntimeOwnershipConstructorBits000')
        self.assertEqual(source.count('#check @'),1)
        self.assertEqual(source.count('#print axioms'),1)
        self.assertIn('written 250 (by decide)',source)
        self.assertIn('written 249 (by decide)',source)
        self.assertIn('change eval base [(2250,1)]',source)
        self.assertNotIn('Satisfies',source)
        self.assertNotIn('checkBits',source)

    def test_changed_order_coefficient_duplicate_or_width_refuses(self):
        for change in ('order','coefficient','duplicate','width','family'):
            values=fixture(2);checked=values[0]
            if change=='order':checked['bits'][0:2]=checked['bits'][1::-1]
            elif change=='coefficient':checked['derived'][checked['bits'][100]]=((2100,2),)
            elif change=='duplicate':checked['bits'][2]=checked['bits'][1]
            elif change=='width':checked['bits'].pop()
            else:checked['metadata']['schema']='pending'
            with self.subTest(change=change),self.assertRaises(RelationError):self.render(values)


if __name__=='__main__':unittest.main()
