"""Pinned native map program and byte parity interfaces remain explicit."""
from pathlib import Path
import re,unittest

REPO=Path(__file__).resolve().parents[1];RUNTIME=Path('C:/src/shieldd-pr160-844389ee')


class NativeProgramTests(unittest.TestCase):
    def test_pinned_native_source_keeps_sqrt_failure_and_exact_parity_boundaries(self):
        native=(RUNTIME/'crates/crypto/circuits/src/map.rs').read_text()
        body=native[native.index('pub fn to_prime('):native.index('/// Unique QR choice')]
        self.assertIn('if let Some(y) = gx1.sqrt()',body)
        self.assertIn('gx2.sqrt()\n                .expect(',body)
        self.assertIn('(y.encode()[31] & 1 == 1) != square',body)
        self.assertIn('if denominator == Scalar::zero()',body)
        self.assertIn('for _ in 0..3',body)
        primitive=(RUNTIME/'crates/crypto/primitives/src/map.rs').read_text()
        self.assertIn('tv * gx1).sqrt().unwrap_or(Fq::ZERO)',primitive)
        self.assertIn('Choice::from(y.to_bytes()[0] & 1) ^ square',primitive)
        self.assertIn('.clear_cofactor()',primitive)
        self.assertNotIn('ensure!',primitive)

    def test_four_audited_program_exports_have_only_global_native_contracts(self):
        source=(REPO/'circuits/ShielddSecurity/ElligatorNativeProgram.lean').read_text()
        checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(checks),4);self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        declaration=source[source.index('theorem source_defined'):].split(':=',1)[0]
        self.assertIn('ElligatorNativeRoots.SqrtAPI F',declaration)
        self.assertIn('(fiveEuler :',declaration)
        for forbidden in ('(expected','(selectedRoot','(nativeSquare','(nativePoint','(satisfied','(nonidentity'):
            self.assertNotIn(forbidden,declaration)
        self.assertIn('Option (Group.Point F)',source)
        self.assertIn('GroupScalarCodec.low_byte_bit',source)
        self.assertIn('set_option maxHeartbeats 250000',source)

    def test_byte_parity_normalization_matches_all_source_choices(self):
        for decoded in (0,1,2,255,256,257,65535):
            byte = decoded % 256
            for choice in (False,True):
                encoded_sign = -1 if ((byte % 2 == 1) != choice) else 1
                field_sign = 1 if ((decoded % 2 == 1) == choice) else -1
                self.assertEqual(encoded_sign,field_sign)
        source=(REPO/'circuits/ShielddSecurity/ElligatorNativeProgram.lean').read_text()
        self.assertIn('rw [low_byte_parity codec writer root]',source)
        self.assertIn('ElligatorNativeRoots.choice,Option.getD_some',source)


if __name__=='__main__':unittest.main()
