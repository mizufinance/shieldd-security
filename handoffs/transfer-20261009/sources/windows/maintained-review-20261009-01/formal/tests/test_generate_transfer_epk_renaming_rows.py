"""Small row-template tests only; no accepted EPK capture or kernel claim."""
import unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_renaming_rows as bounded
from circuits import generate_transfer_epk_fixed_renaming as old,transfer_relation as relation


class EpkRenamingRowTests(unittest.TestCase):
    def test_canonical_authored_order_uses_bit_then_product_chunks_and_unsigned(self):
        from circuits import transfer_recovery_canonical as comparator
        roles=[dict(roles=['boolean'+str(i)],row=2000+i) for i in range(252)]
        roles += [dict(roles=[key],row=9000+i) for i,key in enumerate(('constant-copy','reconstruction','endpoint'))]
        products=[dict(step=i,rows=[100+2*i,101+2*i]) for i in range(1,252)]
        all_indices={item['row'] for item in roles}|{index for item in products for index in item['rows']}
        source=dict(canonical_raw={index:(((100,1),),()) for index in all_indices},
                    scalar=dict(bit_start=100,value=99),checked=dict(parent=dict(constant_copy=200692)),
                    chunks=[dict(metadata=dict(constant_copy=200692))])
        with patch.object(comparator,'_chain',return_value=(dict(templates=roles,products=products),all_indices)):
            indices=old._canonical_indices(source)
        self.assertEqual(indices[:16],list(range(2000,2016)))
        self.assertEqual(indices[16:46],list(range(102,132)))
        self.assertEqual(indices[-3:],[9000,9001,9002])
        self.assertNotEqual(indices,sorted(all_indices))
        block,pair,raw,target=self.fixture(7)
        raw[0]=(((100,relation.MODULUS-1),),());target[20]=(((500,relation.MODULUS-1),),())
        modules=bounded.generate_block(1,126,block,pair,raw,target,maximum_rows=2)
        self.assertIn(f'(500, {relation.MODULUS-1})',modules[0][1])
        self.assertNotIn('(500, (-1 : Int))',modules[0][1])

    def fixture(self,count=7):
        source={i:(((100+i,1),),()) for i in range(count)}
        target={20+i:(((500+i,1),),()) for i in range(count)}
        pair=dict(original_row_map=[(i,20+i) for i in range(count)],restricted_map=[(100+i,500+i) for i in range(count)])
        block=dict(module='RuntimeTransferEpk0Canonical',definition='originalRows',indices=list(range(count)))
        return block,pair,source,target

    def test_small_legacy_output_unchanged(self):
        block,pair,source,target=self.fixture(2)
        self.assertEqual(bounded.generate_block(1,126,block,pair,source,target),[old._row_source(1,126,block,pair,source,target)])

    def test_parts_bounded_and_symbolic_assembly(self):
        block,pair,source,target=self.fixture()
        modules=bounded.generate_block(1,126,block,pair,source,target,maximum_rows=2)
        self.assertEqual(len(modules),5)
        for _,text in modules[:-1]:
            self.assertEqual(text.count('#print axioms exact_rows'),1)
            self.assertLessEqual(text.count('⟨'),2)
        parent=modules[-1][1]
        self.assertIn('List.take_append_drop',parent)
        self.assertIn('congrArg₂',parent)
        self.assertNotIn(':= by decide',parent)
        self.assertEqual(modules[-1][0],'RuntimeTransferEpk1RenamingRows126')

    def test_changed_actual_coefficient_and_other_wide_basis_refuse(self):
        block,pair,source,target=self.fixture()
        changed=dict(target);changed[20]=(((500,2),),())
        with self.assertRaises(relation.RelationError):bounded.generate_block(1,126,block,pair,source,changed,maximum_rows=2)
        with self.assertRaises(relation.RelationError):bounded.generate_block(1,0,block,pair,source,target,maximum_rows=2)
        with self.assertRaises(relation.RelationError):bounded.generate_block(True,126,block,pair,source,target)

    def test_window_copylink_repeat_preserves_exact_old_order_and_multiplicity(self):
        from circuits.transfer_fixed_spend import canonical
        link=(canonical([(0,1),(200692,-1)]),())
        source={0:link,1:(((100,1),),())};target={20:link,21:(((500,1),),())}
        pair=dict(original_row_map=[(0,20),(1,21)],restricted_map=[(0,0),(100,500),(200692,200692)])
        block=dict(module='RuntimeTransferEpk0FixedWindow000',definition='rawRows',indices=[0,1,0])
        result=bounded.generate_block(1,0,block,pair,source,target)
        self.assertEqual(result,[old._row_source(1,0,block,pair,source,target)])
        self.assertIn('def originalRows : List Nat := [20, 21, 20]',result[0][1])
        for indices in ([1,0,1],[0,0,1,0],[True,1,0]):
            changed={**block,'indices':indices}
            with self.assertRaises(relation.RelationError):bounded.generate_block(1,0,changed,pair,source,target)
        with self.assertRaises(relation.RelationError):bounded.generate_block(1,126,block,pair,source,target)

if __name__=='__main__':unittest.main()
