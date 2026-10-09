import re
import unittest
from circuits import generate_transfer_ownership_native_constructor as generator
from circuits.transfer_relation import RelationError


class NativeConstructorTemplateTests(unittest.TestCase):
    def test_private_membership_covers_exact252_columns_in_small_chunks(self):
        source=generator._bit_columns(2000)
        checks=[(int(start),int(width)) for start,width in re.findall(r"List.range' (\d+) (\d+)\)\.all",source)]
        self.assertEqual(len(checks),16)
        self.assertLessEqual(max(width for _,width in checks),16)
        self.assertEqual([column for start,width in checks for column in range(start,start+width)],list(range(2000,2252)))
        self.assertNotIn("List.range' 2000 252).all",source)

    def test_actual_proof_template_keeps_three_exports_and_explicit_alias_reduction(self):
        name,source=generator._render(1996,2000,1994,1995,200692)
        self.assertEqual(name,'RuntimeOwnershipNativeConstructor')
        self.assertEqual(source.count('#check @'),3)
        self.assertEqual(source.count('#print axioms'),3)
        self.assertEqual(source.count('dsimp only [ivk]'),3)
        self.assertIn('List.not_mem_nil,or_false',source)
        self.assertNotRegex(source,r'namespace \w+ :=')
        statement=source.split('theorem native_windows_complete',1)[1].split(' := by',1)[0]
        self.assertNotIn('Satisfies',statement.split(' :\n')[0])
        self.assertNotIn('native_bit_values : ∀ index < 255',source)

    def test_malformed_template_columns_refuse(self):
        for values in ((1996,2000,1994,1995,True),(1996,2000,1994,1996,200692),(1996,2001,1994,1995,200692),(-1,2000,1994,1995,200692)):
            with self.subTest(values=values),self.assertRaises(RelationError):
                generator._render(*values)


if __name__=='__main__':unittest.main()
