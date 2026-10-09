import unittest
from circuits import generate_transfer_spend_auth_generator as generator
from circuits.transfer_relation import RelationError


class SpendAuthGeneratorSourceTests(unittest.TestCase):
    def test_exact_signed_template_operand(self):
        name, text = generator.generate((generator.X, generator.SIGNED_Y))
        self.assertEqual(name, 'RuntimeTransferSpendAuthGenerator')
        self.assertEqual(text.count('#check @'), 3)
        self.assertEqual(text.count('#print axioms '), 3)
        self.assertIn('polynomial_certificate', text)
        self.assertIn('ShielddNativeSdkRaw.generator', text)
        self.assertIn('NativeSpendAuthGenerator.generator_coordinates', text)
        self.assertNotIn('(baseMeaning :', text)
        self.assertNotIn('(exactOrder :', text)
        self.assertNotIn('(satisfied :', text)

    def test_signed_encoding_and_roles_are_not_interchangeable(self):
        for base in ((generator.X, generator.Y), (generator.X+1, generator.SIGNED_Y),
                     (generator.X, generator.SIGNED_Y+1), (True, generator.SIGNED_Y),
                     [generator.X, generator.SIGNED_Y], (), None):
            with self.subTest(base=base), self.assertRaises(RelationError):
                generator.generate(base)


if __name__ == '__main__':
    unittest.main()
