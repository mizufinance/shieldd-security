"""Small LC/ownership refusals only; no fake accepted48 or runtime proof."""
import unittest
from circuits import transfer_epk_fixed_renaming as renaming,transfer_relation as relation


class EpkRenamingTests(unittest.TestCase):
    def test_restricted_injection_and_disjoint_total_extension(self):
        columns=renaming._Map({0,1,2,6,200692})
        columns.add(100,500);columns.add(101,501)
        self.assertEqual(columns.permutation(),[(100,500),(101,501),(500,100),(501,101)])
        with self.assertRaisesRegex(relation.RelationError,'injection'):columns.add(102,500)
        with self.assertRaisesRegex(relation.RelationError,'conflicting'):columns.add(100,502)
        with self.assertRaisesRegex(relation.RelationError,'protected'):columns.add(6,502)
        with self.assertRaisesRegex(relation.RelationError,'protected'):columns.add(102,2)
        with self.assertRaises(relation.RelationError):columns.add(True,502)

    def test_overlapping_moving_supports_refuse_optional_optimization(self):
        columns=renaming._Map({0,1,2,6,200692})
        columns.add(100,500);columns.add(500,100)
        with self.assertRaisesRegex(relation.RelationError,'full fallback'):columns.permutation()

    def test_original_rows_require_exact_coefficients_arity_and_coverage(self):
        columns=renaming._Map({0,1,2,6,200692});columns.add(100,500);columns.add(101,501)
        original={7:(((0,1),(100,3)),((101,4),)),8:(((101,1),),())}
        target={29:(((0,1),(500,3)),((501,4),)),30:(((501,1),),())}
        self.assertEqual(renaming._rows(columns,original,target),[(7,29),(8,30)])
        changed={**target,29:(((0,1),(500,relation.MODULUS-3)),((501,4),))}
        with self.assertRaisesRegex(relation.RelationError,'correspondence'):renaming._rows(columns,original,changed)
        with self.assertRaisesRegex(relation.RelationError,'row count'):renaming._rows(columns,original,{29:target[29]})
        with self.assertRaisesRegex(relation.RelationError,'unmapped'):columns.lc(((102,1),))

    def test_stage_operands_and_order_cannot_be_replaced_by_owned_write_names(self):
        columns=renaming._Map({0,1,2,6,200692});columns.add(100,500)
        left=dict(kind='product',role='xx',left=((100,1),),right=((0,2),),remainder=(),output=101,auxiliary=102,rows=[7,8])
        right=dict(kind='product',role='xx',left=((500,1),),right=((0,2),),remainder=(),output=501,auxiliary=502,rows=[29,30])
        renaming._stage(columns,left,right)
        with self.assertRaisesRegex(relation.RelationError,'LC/coefficient'):
            renaming._stage(columns,left,dict(right,right=((0,3),)))
        with self.assertRaisesRegex(relation.RelationError,'schema/kind/order'):
            renaming._stage(columns,left,dict(right,kind='quotient'))
        with self.assertRaisesRegex(relation.RelationError,'physical row arity'):
            renaming._stage(columns,left,dict(right,rows=[29]))

    def test_unqualified_public_ingress_refuses_without_an_ordinary_stream(self):
        with self.assertRaises(relation.RelationError):renaming.plan(b'{}\n',[],{}, {},{})


if __name__=='__main__':unittest.main()
