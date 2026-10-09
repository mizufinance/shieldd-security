"""Actual row support and same-assignment frame; no native admission claim."""
import io, re, unittest
from circuits import transfer_asset_map as maps, transfer_asset_map_completion as completion
from circuits import transfer_asset_map_inverse_frame as frame
from circuits import transfer_asset_generator_nonidentity as inverse
from tests.test_transfer_asset_generator_nonidentity import inverse_fixture
from tests.test_asset_asserted_squares import defer_captured
from tests.test_transfer_asset_map import square_root, P


def fixture():
    data, caller, stream, builder, _ = inverse_fixture(True)
    parent, caller, raw, builder = defer_captured(data, caller, stream.getvalue(), builder)
    data = inverse.derived_map_view(parent, caller)['map_data']
    return data, maps.extract(data, io.BytesIO(raw), caller), parent, inverse.extract(parent, io.BytesIO(raw), caller), caller, builder


class InverseFrameTests(unittest.TestCase):
    def test_inverse_writes_preserve_all_constructed_map_rows_and_shared_columns(self):
        data, extracted, parent, inverse_extracted, caller, builder = fixture()
        recipe = frame.plan(data, extracted, parent, inverse_extracted, caller)
        base = dict(builder.rho);base.update({1:83, 2:97})
        rho = completion.construct(data, extracted, caller, base, square_root)['assignment']
        evaluate = lambda terms: sum(rho.get(c,0)*n for c,n in terms) % P
        x = evaluate(recipe['inverse']['denominator'])
        self.assertNotEqual(x,0)
        q, product, auxiliary = recipe['writes']
        old = dict(rho)
        rho.update({q:pow(x,-1,P), product:1, auxiliary:(pow(x,-1,P)-x)**2 % P})
        for row in recipe['map']['recipe']['raw'].values():
            self.assertEqual(evaluate(row[0])**2 % P, evaluate(row[1]))
        for row in recipe['inverse']['raw'].values():
            self.assertEqual(evaluate(row[0])**2 % P, evaluate(row[1]))
        self.assertTrue(all(rho[c]==value for c,value in old.items() if c not in recipe['writes']))
        self.assertEqual([rho[1],rho[2]],[83,97])

    def test_bounded_certificates_and_symbolic_bits_have_no_desired_truth_premise(self):
        data, extracted, parent, inverse_extracted, caller, _ = fixture()
        name, source = frame.generate(data, extracted, parent, inverse_extracted, caller)
        self.assertEqual(name,'RuntimeTransferAssetMapInverseFrame')
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source), re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('List.mem_range\'.mp inRange',source)
        self.assertNotIn('def rawRows',source)
        declaration = source[source.index('theorem map_rows_complete'):].split(':=',1)[0]
        for forbidden in ('(satisfied','(legal','(nativeInput','(expected','(nonidentity'):
            self.assertNotIn(forbidden,declaration)
        self.assertIn('NativeCompletion.complete_rows',source)
        self.assertIn('NativeCompletion.rawChunks,List.mem_cons,List.not_mem_nil,or_false] at inChunks',source)
        self.assertNotIn('List.mem_cons,List.mem_singleton',source)


if __name__ == '__main__':
    unittest.main()
