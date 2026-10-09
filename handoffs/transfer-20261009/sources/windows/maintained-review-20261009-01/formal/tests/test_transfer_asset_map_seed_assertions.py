"""Real original Boolean/parity rows, both branches and exceptional zero."""
import copy,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_seed_assertions as assertions
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture,square_root


class SeedAssertionTests(unittest.TestCase):
    def test_computed_native_branches_preserve_original_assertions(self):
        data,caller,stream,_,builder=fixture(17)
        extracted=maps.extract(data,stream,caller);recipe=assertions.plan(data,extracted,caller)
        column,coefficient=recipe['seeds']['recipe']['checked']['values']['u'][0]
        branches=set();exceptions=set()
        for u in (0,2,17):
            base=dict(builder.rho);base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:83,2:97,32767:113})
            base.update({c:c+27 for c in recipe['seeds']['recipe']['owned_writes']})
            result=assertions.construct(data,extracted,caller,base,square_root);rho=result['assignment']
            choice=rho[recipe['seeds']['other']['choice']];branches.add(choice)
            zero=rho[recipe['seeds']['other']['zero']];exceptions.add(zero)
            self.assertEqual(rho[recipe['seeds']['bits'][0]],choice)
            value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            self.assertTrue(all(value(a)**2%maps.P==value(b) for a,b in recipe['raw'].values()))
            self.assertEqual([rho[c] for c in (0,1,2,32000,32767)],[1,83,97,1,113])
            self.assertFalse(result['proof'])
        self.assertEqual(branches,{0,1});self.assertEqual(exceptions,{0,1})

    def test_actual_row_refusal_and_export_premises(self):
        data,caller,stream,_,_=fixture(17)
        extracted=maps.extract(data,stream,caller);recipe=assertions.plan(data,extracted,caller)
        damaged=copy.deepcopy(extracted)
        damaged['selected_rows']=[row for row in damaged['selected_rows'] if row['row']!=recipe['indices'][2]]
        with self.assertRaises(relation.RelationError):assertions.plan(data,damaged,caller)
        name,source=assertions.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapSeedAssertions')
        self.assertEqual(source.count('#check @'),8)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        declaration=source[source.index('theorem complete_rows'):].split(':=',1)[0]
        for forbidden in ('(satisfied','(parity','(nativeOutput','(firstNonzero'):
            self.assertNotIn(forbidden,declaration)
        self.assertIn('selected_square_parity cardinality',source)
        self.assertIn('expectedRows,List.mem_cons,List.not_mem_nil,or_false] at member',source)


if __name__=='__main__':unittest.main()
