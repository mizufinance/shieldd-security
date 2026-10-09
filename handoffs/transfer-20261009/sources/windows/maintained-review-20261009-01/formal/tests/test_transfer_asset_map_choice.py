"""Source/row/native-field fixture joins; generated kernels remain unrun."""
import copy
import io
import re
import unittest
from circuits import transfer_asset_map as maps, transfer_asset_map_choice as choice
from circuits import transfer_asset_map_curve as curve, transfer_relation as relation
from tests.test_transfer_asset_map import fixture
from tests.test_asset_asserted_squares import defer_captured


class ChoiceJoinTests(unittest.TestCase):
    def test_two_assertion_lowerings_and_both_choices(self):
        choices=set()
        for u in (0,2,17):
            data,caller,stream,_,b=fixture(u)
            variants=[(data,caller,stream.getvalue(),b),defer_captured(data,caller,stream.getvalue(),b)]
            for data,caller,raw,b in variants:
                selected=maps.extract(data,io.BytesIO(raw),caller)
                checked=maps.inspect_metadata(data,caller)
                v=checked['values'];evaluate=lambda lc:sum(b.rho[c]*n for c,n in lc)%relation.MODULUS
                scalar=evaluate(v['square']);choices.add(scalar)
                gx=evaluate(v['gx1']);self.assertNotEqual(gx,0)
                # Independent prime-field Euler classification checks the
                # captured Boolean and source equations, not source text shape.
                self.assertEqual(scalar,int(pow(gx,(relation.MODULUS-1)//2,relation.MODULUS)==1))
                x,y=evaluate(v['x']),evaluate(v['y'])
                self.assertEqual(y*y%relation.MODULUS,((x+maps.C1)*x+maps.C2)*x%relation.MODULUS)
                self.assertEqual(y%2,scalar)
                name,source=choice.generate(data,selected,caller)
                self.assertEqual(name,'RuntimeTransferAssetMapChoice')
                exports=re.findall(r'#check @([A-Za-z0-9_]+)',source)
                self.assertEqual(len(exports),15)
                self.assertEqual(exports,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
                self.assertIn('ElligatorNative.choice_unique',source)
                self.assertIn('RuntimeElligatorAlgebra.first_cubic_nonzero',source)
                self.assertIn('sqrtSpecification : nativeOption = true',source)
                self.assertIn('norm_num only at selected difference',source)
                self.assertIn('change eval rho x = if choice rho then eval rho x1 else eval rho x2 at point',source)
                self.assertIn('change eval rho gx2 = eval rho tv * eval rho gx1 at alternative',source)
                self.assertIn('rw [selected,multiplied,difference,bit]',source)
                self.assertNotIn('(cubic :',source)
                self.assertNotIn('(selectedRoot :',source)
                self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
                _,joined=curve.generate(data,selected,caller)
                self.assertIn('image_on_curve',joined)
                self.assertNotIn('(root :',joined)
                bad=copy.deepcopy(selected);bad['selected_rows'].pop()
                with self.assertRaises(relation.RelationError):choice.generate(data,bad,caller)
        self.assertEqual(choices,{0,1})


if __name__=='__main__':unittest.main()
