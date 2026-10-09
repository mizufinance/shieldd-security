"""Original numeric row completion and bounded deferred inverse support."""
import re
import unittest
from unittest.mock import patch

from circuits import transfer_asset_map as maps,transfer_asset_map_completion as completion
from circuits import transfer_asset_map_materialization_sequence as sequence
from tests.test_transfer_asset_map import fixture


class MapNumericSequenceTests(unittest.TestCase):
    def test_arbitrary_native_seed_values_complete_only_original_numeric_rows(self):
        data,caller,stream,_,builder=fixture(17)
        extracted=maps.extract(data,stream,caller)
        recipe=completion.plan(data,extracted,caller)
        base=dict(builder.rho)
        base.update({column:column*103+71 for column in recipe['seeds'].values()})
        base.update({1:179,2:191,32767:211})
        result=sequence.construct_numeric(data,extracted,caller,base)
        rho=result['assignment'];evaluate=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
        self.assertFalse(result['proof'])
        self.assertEqual(set(result['plan']['original_partition']),set(recipe['material_rows']))
        self.assertTrue(all(evaluate(recipe['raw'][i][0])**2%maps.P==evaluate(recipe['raw'][i][1])
                            for i in recipe['material_rows']))
        self.assertTrue(all(rho[column]==base[column] for column in recipe['seeds'].values()))
        self.assertEqual([rho[c] for c in (0,1,2,32000,32767)],[1,179,191,1,211])
        # Arbitrary seeds deliberately need not satisfy QR/parity/inverse
        # assertions; numeric completeness cannot promote them to full-map truth.
        self.assertTrue(any(evaluate(a)**2%maps.P!=evaluate(b) for a,b in recipe['raw'].values()))

    def test_deferred_inverse_holes_receive_bounded_certificates(self):
        data,caller,stream,_,_=fixture(17)
        extracted=maps.extract(data,stream,caller)
        recipe=completion.plan(data,extracted,caller)
        quotient_pairs={tuple(cert['rows'][:2]) for cert in maps.certificates(data,extracted,caller)['quotients']}
        moved=[step for step in recipe['steps'] if tuple(step['rows']) in quotient_pairs]
        self.assertEqual(len(moved),4)
        deferred=dict(recipe,steps=[step for step in recipe['steps'] if step not in moved]+moved)
        with patch.object(completion,'plan',return_value=deferred):
            planned=sequence.plan(data,extracted,caller)
            self.assertTrue(any(part['exceptions'] for part in planned['parts']))
            self.assertTrue(all(len(part['exceptions'])<=8 for part in planned['parts']))
            modules=sequence.generate_supports(data,extracted,caller)
            name,source=sequence.generate(data,extracted,caller)
            self.assertEqual(len(modules),len(planned['parts']))
            self.assertEqual(name,'RuntimeTransferAssetMapNumericConstruction')
            self.assertIn('CompilerSequenceCompletion.preserves_rows',source)
            self.assertIn('CompilerSequenceCompletion.run_append',source)
            self.assertIn('simp only [rawChunks,List.mem_cons,List.not_mem_nil,or_false] at present',source)
            self.assertIn(f'  · exact final{len(planned["parts"])-1} row inside',source)
            statement=source[source.index('theorem complete {'):]
            self.assertNotIn('(satisfied',statement[:statement.index(':= by')])
            self.assertEqual(len(re.findall(r'#check @',source)),len(planned['parts'])+5)
            for text in [source,*modules.values()]:
                self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',text),
                                 re.findall(r'#print axioms ([A-Za-z0-9_]+)',text))
                self.assertNotRegex(text,r'\b(sorry|admit|axiom|native_decide)\b')
        # Structural freshness refusal, independently from assignment values.
        broken=dict(deferred,steps=[dict(deferred['steps'][0],writes=[3]),*deferred['steps'][1:]])
        with patch.object(completion,'plan',return_value=broken):
            with self.assertRaisesRegex(Exception,'seed allocation fence|suffix freshness'):
                sequence.plan(data,extracted,caller)


if __name__=='__main__':unittest.main()
