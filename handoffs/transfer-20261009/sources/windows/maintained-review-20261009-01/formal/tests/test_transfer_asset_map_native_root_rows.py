"""Original fused QR/selected-square semantics across both native choices."""
import io,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_native_root_rows as roots
from circuits import transfer_asset_map_completion as completion,transfer_relation as relation
from tests.test_asset_asserted_squares import deferred_fixture
from tests.test_transfer_asset_map import fixture,square_root


class NativeRootRowsTests(unittest.TestCase):
    def test_actual_assertions_and_semantic_root_perturbations(self):
        data,caller,raw,builder=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        recipe=roots.plan(data,extracted,caller);v=recipe['recipe']['checked']['values']
        column,coefficient=v['u'][0];branches=set()
        for u in (0,2,17):
            base=dict(builder.rho);base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:83,2:97})
            base.update({c:c+33 for c in recipe['recipe']['owned_writes']})
            result=completion.construct(data,extracted,caller,base,square_root);rho=result['assignment']
            value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            branches.add(value(v['square']))
            self.assertTrue(all(value(a)**2%maps.P==value(b) for a,b in recipe['raw'].values()))
            qr=recipe['recipe']['seeds']['qrRoot'];rho[qr]=(rho[qr]+1)%maps.P
            # Preserve the preceding square materialization after perturbing
            # its operand. The independently required fused sum row then fails.
            step=recipe['qr_square'];rho[step['output']]=(value(step['input'])**2-value(step['remainder']))%maps.P
            a,b=recipe['raw'][recipe['indices'][0]]
            self.assertNotEqual(value(a)**2%maps.P,value(b))
            root=recipe['recipe']['seeds']['selectedRoot'];rho[root]=(rho[root]+1)%maps.P
            a,b=recipe['raw'][recipe['indices'][1]]
            self.assertNotEqual(value(a)**2%maps.P,value(b))
        self.assertEqual(branches,{0,1})

    def test_closed_v2_source_shape_and_constructive_export_premises(self):
        data,caller,stream,_,_=fixture(17)
        extracted=maps.extract(data,stream,caller)
        with self.assertRaisesRegex(relation.RelationError,'deferred-square'):
            roots.plan(data,extracted,caller)
        data,caller,raw,_=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        name,source=roots.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapNativeRootRows')
        self.assertEqual(source.count('#check @'),13)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertIn('NativeSeeds.numeric_complete',source)
        self.assertIn('NativeSeeds.computed_roots cardinality',source)
        self.assertIn('NativeSeeds.selected_square_parity cardinality',source)
        self.assertIn('expectedRows,List.mem_cons,List.not_mem_nil,or_false] at member',source)
        self.assertIn('change eval (RuntimeTransferAssetMapNativeFirstRows.finalAssignment codec api rho)',source)
        self.assertIn('RuntimeTransferAssetMapFirstCubicConstruction.tv *',source)
        self.assertIn('simpa only [Int.cast_ofNat] using actual',source)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        for theorem in ('qr_product_value','selected_target_value','complete_rows'):
            declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
            for forbidden in ('(satisfied','(nativeSquare','(expectedRoot','(desiredOutput'):
                self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
