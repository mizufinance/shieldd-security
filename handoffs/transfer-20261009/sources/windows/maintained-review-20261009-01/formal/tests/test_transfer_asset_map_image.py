"""Bounded actual product/assertion composition source, no kernel claim."""
import copy
import io
import re
import unittest
from circuits import transfer_asset_map as maps, transfer_asset_map_image as image
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture
from tests.test_asset_asserted_squares import deferred_fixture


class ImageJoinTests(unittest.TestCase):
    def test_actual_direct_square_and_materialized_variants(self):
        data,caller,raw,_=deferred_fixture()
        variants=[(data,caller,raw)]
        old,owner,stream,_,_=fixture(17);variants.append((old,owner,stream.getvalue()))
        for data,caller,raw in variants:
            extracted=maps.extract(data,io.BytesIO(raw),caller)
            name,source=image.generate(data,extracted,caller)
            self.assertEqual(name,'RuntimeTransferAssetMapRationalImage')
            checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
            self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
            self.assertEqual(len(checks),16)
            self.assertIn('exact coordinates.trans (Elligator.rational_point_sound',source)
            self.assertIn('Compiler.checked_assertion_sound',source)
            self.assertIn('ScalarRows.checked_product_sound',source)
            self.assertIn('set_option maxHeartbeats 500000',source)
            # The native fused source LC may contain a constant plus several
            # private columns. Normalize both the row-derived facts and target
            # before combining the three total-inverse equations.
            self.assertIn('at p a i ⊢',source)
            self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
            statement=source[source.index('theorem rational_image'):source.index('theorem rational_image')+420]
            self.assertIn('(satisfied : Satisfies rho rawRows)',statement)
            self.assertNotIn('(root :',statement)
            self.assertNotIn('(coordinates :',statement)
            altered=copy.deepcopy(extracted);altered['selected_rows'].pop()
            with self.assertRaises(relation.RelationError):image.generate(data,altered,caller)


if __name__=='__main__':unittest.main()
