"""Full selected map closure is strict about every actual original row."""
import copy,io,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_completion as completion
from circuits import transfer_asset_map_native_completion as native,transfer_relation as relation
from tests.test_asset_asserted_squares import deferred_fixture
from tests.test_transfer_asset_map import square_root


class NativeCompletionTests(unittest.TestCase):
    def test_full_original_partition_and_native_owned_assignment(self):
        data,caller,raw,builder=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        plan=native.plan(data,extracted,caller)
        self.assertEqual(len(plan['indices']),870);self.assertEqual([len(g) for g in plan['groups']],[858,3,1,2,3,1,1,1])
        self.assertEqual(set(plan['indices']),set(plan['recipe']['raw']))
        column,coefficient=plan['recipe']['checked']['values']['u'][0]
        for u in (0,2,17):
            base=dict(builder.rho);base.update({column:u*pow(coefficient,-1,maps.P)%maps.P,1:83,2:97,40001:101})
            base.update({c:31*c+79 for c in plan['recipe']['owned_writes']})
            rho=completion.construct(data,extracted,caller,base,square_root)['assignment']
            value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            for group in plan['groups']:
                self.assertTrue(all(value(plan['recipe']['raw'][i][0])**2%maps.P==value(plan['recipe']['raw'][i][1]) for i in group))
            outside=set(base)-set(plan['recipe']['owned_writes'])
            self.assertTrue(all(rho[c]==base[c] for c in outside))
            if u==0:self.assertEqual(tuple(value(lc) for lc in plan['recipe']['checked']['points'][3]),(0,1))

    def test_missing_original_assertion_refuses_and_no_desired_truth_premises(self):
        data,caller,raw,_=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        plan=native.plan(data,extracted,caller);damaged=copy.deepcopy(extracted)
        missing=plan['groups'][-1][0]
        damaged['selected_rows']=[r for r in damaged['selected_rows'] if r['row']!=missing]
        with self.assertRaises(relation.RelationError):native.plan(data,damaged,caller)
        name,source=native.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapNativeCompletion');self.assertEqual(source.count('#check @'),4)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('CanonicalSequence.assignment_equal',source)
        self.assertIn('rawChunks.flatten',source)
        self.assertIn('SeedAssertions.complete_rows cardinality codec api rho linked row inChunk',source)
        self.assertIn('NativeRationalRows.complete_rows codec api rho one four linked row inChunk',source)
        self.assertNotIn('SeedAssertions.complete_rows cardinality codec api rho one',source)
        self.assertNotIn('NativeRationalRows.complete_rows cardinality',source)
        self.assertIn('simp only [rawChunks,List.mem_cons,List.not_mem_nil,or_false] at present',source)
        for theorem in ('complete_rows','native_cofactor'):
            declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
            for forbidden in ('(satisfied','(expectedPoint','(curve','(nonidentity','(inverseEquation','(nativeChoiceValue'):
                self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
