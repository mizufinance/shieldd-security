import copy,unittest
from unittest.mock import patch
from circuits import generate_transfer_ivk_hash_join as join,transfer_relation as relation
from tests.test_transfer_ivk_reduction_order import fixture


class HashJoinTests(unittest.TestCase):
    def generate(self,plan=None,rows=None,output=((3,1),)):
        plan=plan or fixture();rows=rows or {0:(((3,1),(1980,1),(1981,1),(1993,1)),())}
        accepted=dict(handles=[0,1,2,99],derived={99:output})
        with patch.object(join.hashes,'select_ivk',return_value=(dict(calls=[dict(parameters=dict(width=6))]),dict(constant_copy=60000),[])),\
             patch.object(join.hashes.ivk,'inspect_metadata',return_value=accepted),\
             patch.object(join.reduction,'plan',return_value=plan),\
             patch.object(join.hashes.blocks,'_chunk_plan',return_value=dict(raw=rows)):
            return join.generate(b'ivk',{},b'reduction',{},'params','0'*64)

    def test_constructor_supplies_all_prior_row_truth(self):
        _,source=self.generate()
        self.assertEqual(source.count('#check @'),7)
        self.assertIn('ScalarReductionFrame.rows',source)
        self.assertIn('H.complete_rows'.replace('H.','RuntimeTransferIvkHashOwnedCompletion.'),source)
        self.assertEqual(source.count('private theorem write_chunk'),34)
        self.assertEqual(source.count('private theorem support'),13)
        statement=source[source.index('theorem complete_local_rows'):source.index(' :=',source.index('theorem complete_local_rows'))]
        self.assertNotIn('satisfied',statement)
        self.assertNotIn('constructed',statement)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')

    def test_earlier_seed_and_product_overlap_refused(self):
        for column in (1994,1995,1996,2000,2251,10000):
            with self.subTest(column=column),self.assertRaises(relation.RelationError):
                self.generate(rows={0:(((column,1),),())})

    def test_hash_reduction_lc_alias_refused(self):
        with self.assertRaises(relation.RelationError):self.generate(output=((4,1),))


if __name__=='__main__':unittest.main()
