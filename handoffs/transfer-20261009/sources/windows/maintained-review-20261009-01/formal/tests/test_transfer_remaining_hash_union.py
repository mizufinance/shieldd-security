"""Small physical/source-template fixtures; no runtime or kernel evidence."""
import unittest
from unittest.mock import patch
from circuits import transfer_remaining_hash_union as union
from circuits.transfer_relation import RelationError,MODULUS

unit=lambda column:((column,1),)
def row(index,a,b=()):
    return dict(row=index,a=[[c,f'{v%MODULUS:064x}'] for c,v in a],b=[[c,f'{v%MODULUS:064x}'] for c,v in b])

def fixture():
    copy=200692;left=unit(90);right=unit(91);output=unit(92);auxiliary=unit(93)
    link=(union.canonical([(0,1),(copy,-1)]),())
    square=(left,unit(94))
    required={link:['constant-copy'],square:['square0','shared-square']}
    products=[('fifth',union.combine(left,right,-1),union.combine(left,right),output)]
    rows=[row(2,*link),row(10,*square),row(11,union.combine(left,right,-1),auxiliary),
          row(12,union.combine(left,right),union.combine(auxiliary,output,4))]
    return rows,required,products

class RemainingHashUnionTests(unittest.TestCase):
    def test_retained_unique_rows_and_shared_square_names(self):
        rows,direct,products=fixture()
        matched=union._match_part(rows,direct,products)
        self.assertEqual(matched['selected_rows'],rows)
        self.assertEqual(matched['templates'][1]['roles'],['square0','shared-square'])
        self.assertEqual(matched['products'],[dict(role='fifth',rows=[11,12])])

    def test_swapped_minus_has_same_mathematical_product(self):
        rows,direct,products=fixture()
        rows[2]['a']=[[c,f'{(-int(v,16))%MODULUS:064x}'] for c,v in rows[2]['a']]
        self.assertEqual(union._match_part(rows,direct,products)['products'][0]['rows'],[11,12])

    def test_missing_duplicate_changed_output_and_reversed_order_refused(self):
        for mode in ('missing','direct','product','output','reverse'):
            rows,direct,products=fixture()
            if mode=='missing':rows.pop()
            elif mode=='direct':rows.append({**rows[1],'row':13})
            elif mode=='product':rows.append({**rows[3],'row':13})
            elif mode=='output':rows[3]['b'][1][1]=f'{5:064x}'
            else:rows[2]['row']=13
            with self.assertRaises(RelationError):union._match_part(rows,direct,products)

    def test_single_union_observer_and_full_identity_shape(self):
        rows,direct,products=fixture();observed=[]
        obj=dict(relation_digest='0'*64,domain_size=262144,full_rows=200770)
        def inspect(stream,expected_relation,row_observer):
            self.assertIs(stream,observed);self.assertEqual(expected_relation,obj['relation_digest'])
            for item in rows:row_observer(item)
            return dict(relation_digest=expected_relation,domain_size=262144,stored_rows=200770)
        with patch.object(union.relation,'inspect',side_effect=inspect) as mocked:
            selected=union._retain(observed,obj,direct,products)
            self.assertEqual(selected['selected_rows'],rows);mocked.assert_called_once()
        obj['full_rows']=200769
        with patch.object(union.relation,'inspect',side_effect=inspect):
            with self.assertRaises(RelationError):union._retain(observed,obj,direct,products)

    def test_folded_source_nodes_have_no_invented_physical_rows(self):
        checked=dict(metadata=dict(constant_copy=200692),nodes={(2,1):(True,(0,3),(1,4))},
            derived={(0,3):((0,3),),(1,4):unit(94),(2,1):((94,3),)})
        direct,products=union._requirements(checked)
        self.assertEqual(len(direct),1);self.assertEqual(products,[])

if __name__=='__main__':unittest.main()
