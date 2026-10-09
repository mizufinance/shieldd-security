"""Exact first native material transport without assuming inverse assertion."""
import io,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_completion as completion
from circuits import transfer_asset_map_native_first_rows as first
from tests.test_asset_asserted_squares import deferred_fixture
from tests.test_transfer_asset_map import square_root


class NativeFirstRowsTests(unittest.TestCase):
    def test_original_inverse_and_first_cubic_from_native_seed(self):
        data,caller,raw,builder=deferred_fixture()
        extracted=maps.extract(data,io.BytesIO(raw),caller);recipe=first.plan(data,extracted,caller)
        self.assertEqual(len(recipe['material']),8);self.assertEqual(recipe['chunks'],[0,37])
        v=recipe['first']['values'];column,coefficient=v['u'][0]
        for u in (0,2,17):
            base=dict(builder.rho);base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:83,2:97})
            base.update({c:17*c+23 for c in recipe['first']['recipe']['owned_writes']})
            built=completion.construct(data,extracted,caller,base,square_root);rho=built['assignment']
            value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            tv=5*u*u%maps.P;x=-maps.C1*pow(1+tv,-1,maps.P)%maps.P
            g=((x+maps.C1)*x+maps.C2)*x%maps.P
            self.assertEqual(value(v['tv']),tv);self.assertEqual(value(v['x1']),x)
            self.assertEqual(value(v['gx1']),g);self.assertNotEqual(g,0)
            row=recipe['first']['recipe']['raw'][recipe['assertion']]
            self.assertEqual(value(row[0])**2%maps.P,value(row[1]))
            self.assertEqual([rho[c] for c in (0,1,2,32000)],[1,83,97,1])

    def test_constructor_not_asserted_first_rows_supply_product_facts(self):
        data,caller,raw,_=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        name,source=first.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapNativeFirstRows')
        self.assertEqual(source.count('#check @'),18)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertIn('NativeSeeds.numeric_complete',source)
        self.assertIn('List.mem_flatten.mpr',source)
        self.assertIn('List.mem_cons_of_mem',source)
        self.assertIn('List.mem_cons_self',source)
        self.assertNotIn('NumericConstruction.rawChunks,List.mem_cons',source)
        self.assertNotIn('List.Sublist',source)
        self.assertIn('native_denominator_nonzero cardinality rho',source)
        self.assertIn('have inputRight := Compiler.canonical_equal',source)
        self.assertIn('RuntimeTransferAssetMapFirstCubicConstruction.input (by decide)',source)
        self.assertIn('rw [inputRight,input_value] at actual',source)
        self.assertIn('RuntimeTransferAssetMapFirstCubicConstruction.tv,RuntimeTransferAssetMapFirstCubicConstruction.nativeTv,Int.cast_ofNat',source)
        self.assertIn('RuntimeTransferAssetMapFirstCubicConstruction.firstX at second',source)
        self.assertIn('rw [first_x_value] at second',source)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        for theorem in ('first_g_value','inverse_target_value','complete_rows'):
            declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
            for forbidden in ('(satisfied','(nativeOutput','(firstNonzero','(inverseEquation'):
                self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
