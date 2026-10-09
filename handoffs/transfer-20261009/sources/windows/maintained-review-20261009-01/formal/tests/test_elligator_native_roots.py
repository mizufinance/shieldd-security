"""Native sqrt option/zero and fallback existence boundaries; no kernel claim."""
from pathlib import Path
import re
import unittest
from tests.test_transfer_asset_map import P,square_root


class NativeRootsTests(unittest.TestCase):
    def test_native_fallback_and_selected_squares_include_zero(self):
        self.assertEqual(pow(5,P//2,P),P-1)
        seen=set()
        for first in (0,1,4,5,25,P-1):
            chosen=square_root(first) is not None
            seen.add(chosen)
            qr=first if chosen else 5*first%P
            qr_root=square_root(qr)
            self.assertIsNotNone(qr_root)
            self.assertEqual(qr_root*qr_root%P,qr)
            for u in (0,1,17):
                selected=first if chosen else 5*u*u*first%P
                root=square_root(selected)
                self.assertIsNotNone(root)
                self.assertEqual(root*root%P,selected)
                if not chosen and u==0:self.assertEqual(root,0)
        self.assertEqual(seen,{False,True})
        # Some(0) is a successful square root, not None/the false branch.
        self.assertEqual(square_root(0),0)

    def test_finite_audited_computed_roots_use_global_api_contract(self):
        source=(Path(__file__).resolve().parents[1]/'circuits/ShielddSecurity/ElligatorNativeRoots.lean').read_text()
        checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertEqual(len(checks),5)
        self.assertIn('set_option maxHeartbeats 180000',source)
        self.assertIn('FiniteField.pow_dichotomy',source)
        self.assertIn('FiniteField.isSquare_iff',source)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        statement=source[source.index('theorem computed_roots'):source.index('#check @alternative_square')]
        self.assertNotIn('(nativeSquare',statement)
        self.assertNotIn('(root :',statement)
        self.assertNotIn('(satisfied',statement)


if __name__=='__main__':unittest.main()
