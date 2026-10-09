"""Native seed construction covers both choices and preserves numeric columns."""
import re
import unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_native_seed_completion as seeds
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture,square_root


class NativeSeedCompletionTests(unittest.TestCase):
    def test_computed_seed_branches_and_exact264_ownership(self):
        data,caller,stream,_,builder=fixture(17)
        extracted=maps.extract(data,stream,caller)
        recipe=seeds.plan(data,extracted,caller)
        self.assertEqual(len(recipe['owned']),264)
        branches=set()
        ucolumn,ucoefficient=recipe['recipe']['checked']['values']['u'][0]
        for u in (0,2,17):
            base=dict(builder.rho)
            base.update({ucolumn:u*pow(ucoefficient,-1,maps.P)%maps.P,1:83,2:97,32767:113})
            base.update({c:7*c+13 for c in recipe['owned']})
            result=seeds.construct_seed(data,extracted,caller,base,square_root)
            rho=result['assignment'];choice=rho[recipe['other']['choice']]
            branches.add(choice);root=rho[recipe['root']]
            self.assertEqual(root%2,choice)
            self.assertEqual(sum(rho[c]*2**i for i,c in enumerate(recipe['bits'])),root)
            self.assertTrue(all(rho[c] in (0,1) for c in recipe['bits']))
            self.assertTrue(all(rho.get(c,0)==v for c,v in base.items() if c not in recipe['owned']))
            self.assertEqual([rho[c] for c in (0,1,2,32000,32767)],[1,83,97,1,113])
            self.assertFalse(result['proof'])
            if u==0:
                self.assertEqual(root,0)
                self.assertEqual(result['native_generator'],(0,1))
                # Local map seed legality does not imply native asset-generator
                # nonidentity. Its independent hash/admission join stays open.
        self.assertEqual(branches,{0,1})
        with self.assertRaisesRegex(relation.RelationError,'sqrt/option specification'):
            seeds.construct_seed(data,extracted,caller,dict(builder.rho),lambda _:1)

    def test_formal_seed_recipe_derives_roots_parity_and_all_double_denominators(self):
        data,caller,stream,_,_=fixture(17)
        extracted=maps.extract(data,stream,caller)
        name,source=seeds.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapNativeSeeds')
        exports=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(exports),36)
        self.assertEqual(exports,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('ElligatorNativeRoots.computed_roots',source)
        self.assertIn('RuntimeTransferAssetMapFirstCubicConstruction.native_first_nonzero',source)
        self.assertIn('Group.shared_inverse_double_sound',source)
        self.assertIn('seedValue,patchAssignment,List.mem_singleton,if_true]',source)
        self.assertIn('RuntimeTransferAssetMapNumericConstruction.seed_values',source)
        for theorem in ('selected_square_parity','native_image_curve','quotient1_denominator_nonzero',
                        'quotient2_denominator_nonzero','quotient3_denominator_nonzero','numeric_complete'):
            declaration=source[source.index('theorem '+theorem):]
            declaration=declaration[:declaration.index(':=')]
            for forbidden in ('(satisfied','(nativeSquare','(firstNonzero','(nativeOutput','(legal'):
                self.assertNotIn(forbidden,declaration)
        self.assertIn('set_option maxHeartbeats 400000',source)
        self.assertIn('set_option maxRecDepth 2048',source)


if __name__=='__main__':unittest.main()
