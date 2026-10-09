"""EPK inverse domain is the independent encryption guard, never statement.ok."""
from pathlib import Path
import re
import unittest

REPO=Path(__file__).resolve().parents[1]
RUNTIME=Path('C:/src/shieldd-pr160-844389ee')


class NativeEphemeralGeneratorTests(unittest.TestCase):
    def test_pinned_native_and_circuit_epk_order(self):
        source=(RUNTIME/'crates/crypto/circuits/src/encryption.rs').read_text()
        native=source[source.index('pub fn encrypt('):source.index('pub fn constrain')]
        guard='*r != Scalar::zero() && *r < Scalar::from_limbs(scalar::ORDER)'
        multiply='let epks = ephemeral.each_ref().map(|r| group::generator().multiply(r));'
        self.assertLess(native.index(guard),native.index(multiply))
        self.assertIn('epk: epks[i].clone()',native)
        circuit=source[source.index('pub fn constrain'):]
        anchors=['&out.sender_core.epk','&out.sender_ext.epk','&out.output_core.epk','&out.output_ext.epk']
        self.assertEqual([circuit.index(a) for a in anchors],sorted(circuit.index(a) for a in anchors))
        self.assertIn('scalar::canonical_bits(ctx, &var(&w.ephemeral[i]))',circuit)
        self.assertIn('generator.multiply_fixed(&bits).assert_equal(epks[i]);',circuit)
        self.assertIn('epks[i].assert_non_identity();',circuit)

    def test_canonical_positive_scalar_and_prime_order_boundary(self):
        # Independent small prime cyclic group checks the generic exact-order
        # argument and its zero endpoint. Every1..r-1 has a nonzero multiple.
        order=11
        self.assertTrue(all((n*3)%order!=0 for n in range(1,order)))
        self.assertEqual((0*3)%order,0)
        self.assertEqual((order*3)%order,0)
        source=(REPO/'circuits/ShielddSecurity/NativeEphemeralGenerator.lean').read_text()
        checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(checks),3)
        self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('codec.roundtrip value',source)
        self.assertIn('GroupByteCodec.native_reader_coordinates',source)
        self.assertIn('GroupNativeGenerator.canonical_multiple_inverse',source)
        self.assertIn('NativeEphemeralAdmission.encryption_success',source)
        declaration=source[source.index('theorem encryption_ephemeral_inverse'):].split(':=',1)[0]
        self.assertIn('(exactOrder : addOrderOf generator = Scalar.order)',declaration)
        self.assertIn('(accepted : NativeEphemeralAdmission.encryptionNative',declaration)
        for forbidden in ('(nonidentity','(epkEquals','(inverseEquation','(statementOk','(satisfied'):
            self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
