"""Original image boundary composes material rows, inverse assertions and link."""
import ast,io,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_completion as completion
from circuits import transfer_asset_map_native_image_rows as image,transfer_asset_map_image as sound
from tests.test_asset_asserted_squares import deferred_fixture
from tests.test_transfer_asset_map import square_root


class NativeImageRowsTests(unittest.TestCase):
    def test_actual_twenty_rows_and_native_exceptional_image(self):
        data,caller,raw,builder=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        recipe=image.plan(data,extracted,caller);v=recipe['recipe']['checked']['values']
        _,source=sound.generate(data,extracted,caller)
        exact=ast.literal_eval(re.search(r'def originalRows : List Nat := (\[[^\n]*\])',source).group(1))
        self.assertEqual(recipe['indices'],exact);self.assertEqual(len(exact),20)
        self.assertEqual(recipe['chunks'],[32,33])
        column,coefficient=v['u'][0]
        for u in (0,2,17):
            base=dict(builder.rho);base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:83,2:97})
            base.update({c:7*c+71 for c in recipe['recipe']['owned_writes']})
            rho=completion.construct(data,extracted,caller,base,square_root)['assignment']
            value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            s,t=value(v['s']),value(v['t']);den=(s+1)*t%maps.P
            expected=(0,1) if not den else (pow(den,-1,maps.P)*(s+1)*s%maps.P,pow(den,-1,maps.P)*t*(s-1)%maps.P)
            actual=tuple(value(lc) for lc in recipe['recipe']['checked']['points'][0])
            self.assertEqual(actual,expected)
            x,y=actual;self.assertEqual((-x*x+y*y-1-maps.D*x*x*y*y)%maps.P,0)
            self.assertTrue(all(value(recipe['recipe']['raw'][i][0])**2%maps.P==value(recipe['recipe']['raw'][i][1]) for i in exact))
            if u==0:self.assertEqual(actual,(0,1))

    def test_complete_image_uses_constructive_material_and_inverse_truth(self):
        data,caller,raw,_=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        name,source=image.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapNativeImageRows');self.assertEqual(source.count('#check @'),8)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('NativeRationalRows.complete_rows',source)
        self.assertIn('NativeSeeds.numeric_complete',source)
        self.assertIn('NativeSeeds.native_image_curve',source)
        self.assertIn('List.mem_cons_of_mem',source)
        self.assertIn('List.mem_cons_self',source)
        self.assertNotIn('NumericConstruction.rawChunks,List.mem_cons',source)
        for theorem in ('image_rows_complete','native_image','native_image_curve'):
            declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
            for forbidden in ('(satisfied','(curve','(expectedPoint','(inverseEquation'):
                self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
