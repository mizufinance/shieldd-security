"""Exact first inverse/cubic construction with independent native arithmetic."""
import re
import unittest

from circuits import transfer_asset_map as maps,transfer_asset_map_first_cubic_completion as cubic
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture


class FirstCubicConstructionTests(unittest.TestCase):
    def test_native_inputs_construct_original_rows_and_preserve_shared_values(self):
        data,caller,stream,_,builder=fixture(17)
        extracted=maps.extract(data,stream,caller)
        recipe=cubic.plan(data,extracted,caller)
        self.assertEqual(len(recipe['raw']),10)
        self.assertEqual(len(recipe['owned']),9)
        self.assertEqual(len(recipe['values']['u']),1)
        column,coefficient=recipe['values']['u'][0]
        for u in (0,1,17,maps.P-1):
            base=dict(builder.rho)
            base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:179,2:191,32767:211})
            base.update({c:103*c+71 for c in recipe['owned']})
            result=cubic.construct(data,extracted,caller,base)
            rho=result['assignment'];evaluate=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            den=(1+5*u*u)%maps.P
            x=-maps.C1*pow(den,-1,maps.P)%maps.P
            first=((x+maps.C1)*x+maps.C2)*x%maps.P
            self.assertEqual(result['native_input'],u)
            self.assertEqual(result['native_first'],first)
            self.assertNotEqual(first,0)
            self.assertEqual(evaluate(recipe['values']['gx1']),first)
            self.assertEqual(evaluate(recipe['quotient']['output']),1)
            self.assertTrue(all(evaluate(a)**2%maps.P==evaluate(b) for a,b in recipe['raw'].values()))
            self.assertTrue(all(rho.get(c,0)==v for c,v in base.items() if c not in recipe['owned']))
            self.assertEqual([rho[c] for c in (0,1,2,32000,32767)],[1,179,191,1,211])
            self.assertFalse(result['proof'])
        with self.assertRaisesRegex(relation.RelationError,'one/copy'):
            cubic.construct(data,extracted,caller,dict(builder.rho) | {32000:0})

    def test_generated_constructor_has_global_parameter_facts_and_complete_audits(self):
        data,caller,stream,_,_=fixture(17)
        extracted=maps.extract(data,stream,caller)
        name,source=cubic.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapFirstCubicConstruction')
        audits=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(audits),24)
        self.assertEqual(audits,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('RuntimeElligatorParameters.negative_z_nonsquare',source)
        self.assertIn('RuntimeElligatorAlgebra.first_cubic_nonzero',source)
        self.assertIn('CompilerSignedCompletion.original_rows',source)
        self.assertIn('set_option maxHeartbeats 400000',source)
        self.assertIn('Compiler.subtract inverseTarget [(0,1)]',source)
        self.assertNotIn('⟨subtract inverseTarget',source)
        self.assertIn('List.mem_singleton,if_true',source)
        self.assertIn('scaled,eval_scale,input_value] at actual',source)
        self.assertIn('firstAdd,first_x_value] at first',source)
        self.assertNotIn('input_value,input_value',source)
        self.assertNotIn('first_x_value,first_x_value',source)
        self.assertIn('simpa only [nativeFirst,Elligator.cubic] using second',source)
        for theorem in ('native_first_nonzero','first_g_nonzero','complete_rows'):
            declaration=source[source.index('theorem '+theorem):]
            declaration=declaration[:declaration.index(':=')]
            self.assertNotIn('(satisfied',declaration)
            self.assertNotIn('(firstNonzero',declaration)
            self.assertNotIn('(coordinate',declaration)
            self.assertNotIn('(root',declaration)


if __name__=='__main__':unittest.main()
