"""Actual cofactor quotients follow native doubling, including identity input."""
import copy,io,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_completion as completion
from circuits import transfer_asset_map_native_double_rows as doubles,transfer_relation as relation
from tests.test_asset_asserted_squares import deferred_fixture
from tests.test_transfer_asset_map import square_root


class NativeDoubleRowsTests(unittest.TestCase):
    def test_three_original_inverse_assertions_and_native_recurrence(self):
        data,caller,raw,builder=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        plans=[doubles.plan(data,extracted,caller,i) for i in range(3)]
        v=plans[0]['recipe']['checked']['values'];column,coefficient=v['u'][0]
        self.assertEqual([p['chunks'] for p in plans],[[33,34,37],[35,36,37],[36,37]])
        for u in (0,2,17):
            base=dict(builder.rho);base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:83,2:97})
            base.update({c:29*c+67 for c in plans[0]['recipe']['owned_writes']})
            rho=completion.construct(data,extracted,caller,base,square_root)['assignment']
            value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            for stage,plan in enumerate(plans):
                point=plan['point'];x,y=(value(lc) for lc in point['input'])
                delta=maps.D*x*x*y*y%maps.P;den=(1+delta)*(1-delta)%maps.P
                self.assertNotEqual(den,0);inv=pow(den,-1,maps.P)
                expected=(2*x*y*(1-delta)*inv%maps.P,(y*y+x*x)*(1+delta)*inv%maps.P)
                self.assertEqual(tuple(value(lc) for lc in point['output']),expected)
                self.assertEqual(value(point['inverse']),inv)
                a,b=plan['recipe']['raw'][plan['assertion']]
                self.assertEqual(value(a)**2%maps.P,value(b))
                if u==0:self.assertEqual(expected,(0,1))
                # Repair the numeric quotient product and its auxiliary after
                # corrupting only the inverse: the original assertion fails.
                changed=dict(rho);inverse=plan['recipe']['seeds']['doubleInverse'+str(stage)]
                changed[inverse]=(changed[inverse]+1)%maps.P
                cv=lambda lc:sum(changed.get(c,0)*n for c,n in lc)%maps.P
                product=plan['products'][-1];step=plan['recipe']['steps'][product['position']]
                left,right=cv(step['left']),cv(step['right'])
                changed[step['output']]=(left*right-cv(step['remainder']))%maps.P
                changed[step['auxiliary']]=(left-right)**2%maps.P
                self.assertNotEqual(cv(a)**2%maps.P,cv(b))
                self.assertEqual([changed[c] for c in (0,1,2,32000)],[1,83,97,1])

    def test_exact_actual_rows_and_independent_native_legality(self):
        data,caller,raw,_=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        plan=doubles.plan(data,extracted,caller,0);damaged=copy.deepcopy(extracted)
        damaged['selected_rows']=[r for r in damaged['selected_rows'] if r['row']!=plan['assertion']]
        with self.assertRaises(relation.RelationError):doubles.plan(data,damaged,caller,0)
        with self.assertRaises(relation.RelationError):doubles.plan(data,extracted,caller,3)
        for stage in range(3):
            name,source=doubles.generate(data,extracted,caller,stage)
            self.assertEqual(name,'RuntimeTransferAssetMapNativeDouble'+str(stage))
            self.assertEqual(source.count('#check @'),26)
            self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
            self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
            self.assertIn('NativeSeeds.quotient'+str(stage+1)+'_denominator_nonzero',source)
            self.assertIn('NativeSeeds.numeric_complete',source)
            self.assertIn('List.mem_cons_of_mem',source)
            self.assertIn('List.mem_cons_self',source)
            self.assertIn('have minusValue : eval',source)
            self.assertIn('change eval (finalAssignment codec api rho) xx =',source)
            self.assertIn('change eval (finalAssignment codec api rho) yy =',source)
            self.assertIn('rw [xxValue,yyValue,plusValue] at actual',source)
            self.assertNotIn('NumericConstruction.rawChunks,List.mem_cons',source)
            for theorem in ('quotient_target_value','output_native','complete_rows'):
                declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
                for forbidden in ('(satisfied','(curve','(denominatorNonzero','(inverseEquation','(expectedPoint'):
                    self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
