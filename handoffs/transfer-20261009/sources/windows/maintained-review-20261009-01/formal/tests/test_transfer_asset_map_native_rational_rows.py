"""Native total inverse owns both zero and ordinary original row branches."""
import copy,io,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_completion as completion
from circuits import transfer_asset_map_native_rational_rows as rational,transfer_relation as relation
from tests.test_asset_asserted_squares import deferred_fixture
from tests.test_transfer_asset_map import square_root


class NativeRationalRowsTests(unittest.TestCase):
    def test_original_assertions_zero_and_regular_inverse_materializations(self):
        data,caller,raw,builder=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        recipe=rational.plan(data,extracted,caller);v=recipe['recipe']['checked']['values']
        self.assertEqual(len(recipe['material']),10);self.assertEqual(recipe['chunks'],[0,32,33])
        column,coefficient=v['u'][0];branches=set()
        for u in (0,2,17):
            base=dict(builder.rho);base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:83,2:97})
            base.update({c:23*c+59 for c in recipe['recipe']['owned_writes']})
            rho=completion.construct(data,extracted,caller,base,square_root)['assignment']
            value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            denominator=value(v['den']);branches.add(denominator==0)
            self.assertEqual(value(v['zero']),int(denominator==0))
            self.assertEqual(value(v['inv']),pow(denominator,-1,maps.P) if denominator else 0)
            self.assertTrue(all(value(a)**2%maps.P==value(b) for a,b in recipe['raw'].values()))
            inverse=recipe['recipe']['seeds']['totalInverse'];rho[inverse]=(rho[inverse]+1)%maps.P
            # Restore every affected actual numeric product/aux row; one of
            # the independent total-inverse assertions must still fail.
            for product in recipe['products'][2:]:
                step=recipe['recipe']['steps'][product['position']]
                left,right=value(step['left']),value(step['right'])
                rho[step['output']]=(left*right-value(step['remainder']))%maps.P
                rho[step['auxiliary']]=(left-right)**2%maps.P
            self.assertTrue(any(value(a)**2%maps.P!=value(b) for a,b in recipe['raw'].values()))
            self.assertEqual([rho[c] for c in (0,1,2,32000)],[1,83,97,1])
        self.assertEqual(branches,{False,True})

    def test_exact_original_assertions_and_no_nonzero_denominator_premise(self):
        data,caller,raw,_=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        recipe=rational.plan(data,extracted,caller);damaged=copy.deepcopy(extracted)
        damaged['selected_rows']=[r for r in damaged['selected_rows'] if r['row']!=recipe['indices'][0]]
        with self.assertRaises(relation.RelationError):rational.plan(data,damaged,caller)
        name,source=rational.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapNativeRationalRows');self.assertEqual(source.count('#check @'),20)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('Elligator.inverse_constraints_complete',source)
        self.assertIn('rw [eval_append,s_value codec api rho one four linked] at actual',source)
        self.assertIn('simp only [exceptional,inv_zero,if_true]',source)
        self.assertIn('NativeSeeds.numeric_complete',source)
        self.assertIn('List.mem_cons_of_mem',source)
        self.assertIn('List.mem_cons_self',source)
        self.assertNotIn('NumericConstruction.rawChunks,List.mem_cons',source)
        self.assertNotIn('List.mem_cons,List.mem_singleton',source)
        for theorem in ('computed_constraints','expected_complete','complete_rows'):
            declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
            for forbidden in ('(satisfied','(nativeOutput','(denominatorNonzero','(inverseEquation'):
                self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
