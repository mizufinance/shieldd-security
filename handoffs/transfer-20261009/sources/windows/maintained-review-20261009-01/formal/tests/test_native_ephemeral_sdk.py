"""Pinned same-object EPK scalar/generator conversion; no capture/row proof claim."""
import re,unittest
from pathlib import Path
from circuits.transfer_canonical_balance import ORDER
ROOT=Path(__file__).parents[1];RUNTIME=Path('C:/src/shieldd-pr160-844389ee')
class NativeEphemeralSdkTests(unittest.TestCase):
    def test_source_uses_caller_fr_reader_and_exact_spend_auth_generator(self):
        caller=(RUNTIME/'crates/core/component/shielded-pool/src/pari.rs').read_text()
        self.assertIn('field(&encoding::field(&value.to_bytes()).expect("Jubjub scalar fits base field"))',caller)
        self.assertIn('randomizer: scalar(opening.r)',caller)
        group=(RUNTIME/'crates/crypto/circuits/src/group.rs').read_text()
        self.assertIn('native_point(&shieldd_sdk_crypto::generators::SPEND_AUTH)',group)
        self.assertIn('bytes.reverse();',group)
        self.assertIn('ScalarReadCfg::AllowZero',group)
        self.assertIn('let bytes = scalar.encode();',group)
    def test_scalar_endpoints_and_native_reader_integer_agree(self):
        for n in [0,1,2,255,256,2**128-1,ORDER-1]:
            sdk_le=n.to_bytes(32,'little');base=int.from_bytes(sdk_le,'little')
            native_be=base.to_bytes(32,'big')
            bits=[bool((native_be[31-i//8]>>(i%8))&1) for i in range(255)]
            self.assertEqual(sum(int(b)<<i for i,b in enumerate(bits)),n)
            self.assertEqual(bits[252:],[False]*3)
            self.assertEqual(int.from_bytes(sdk_le[::-1],'big'),n)
        self.assertEqual(0>0,False)
    def test_four_audited_signatures_and_independent_premises(self):
        source=(ROOT/'circuits/ShielddSecurity/NativeEphemeralSdk.lean').read_text()
        checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(checks),4);self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('GroupNativeSdk.generator_embedding sdk',source)
        self.assertIn('GroupNativeSdk.scalar_canonical codec fq fr decoder scalar',source)
        inverse=source[source.index('theorem native_epk_inverse'):].split(':= by')[0]
        for forbidden in ['(epk :','(nonidentity','(satisfied','(inverseEquation','(outputEqual']:
            self.assertNotIn(forbidden,inverse)
        self.assertIn('addOrderOf (sdk.embed sdk.spendAuth) = Scalar.order',inverse)
        self.assertIn('0 < fr.integer scalar',inverse)