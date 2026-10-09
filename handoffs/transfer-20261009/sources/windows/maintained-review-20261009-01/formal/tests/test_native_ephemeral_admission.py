"""Exact pinned constructor guards, independent of successful statement digest."""
from pathlib import Path
import re,unittest

RUNTIME=Path('C:/src/shieldd-pr160-844389ee');REPO=Path(__file__).resolve().parents[1]


class NativeEphemeralAdmissionTests(unittest.TestCase):
    def test_native_recovery_disclosure_and_both_ownership_guards(self):
        recovery=(RUNTIME/'crates/crypto/circuits/src/recovery.rs').read_text()
        body=recovery[recovery.index('pub fn encrypt('):recovery.index('/// Preserves EPK/DH')]
        self.assertIn('randomizer != Scalar::zero() && randomizer < Scalar::from_limbs(scalar::ORDER)',body)
        self.assertLess(body.index('ensure!('),body.index('let epk ='))
        audit=(RUNTIME/'crates/crypto/circuits/src/audit.rs').read_text()
        body=audit[audit.index('pub fn encrypt('):audit.index('/// Address and checking points')]
        self.assertIn('randomness != Scalar::zero() && randomness < Scalar::from_limbs(scalar::ORDER)',body)
        anchors=['"ownership scalar must be canonical and nonzero"','"identity ownership key"','let published =']
        self.assertEqual([body.index(s) for s in anchors],sorted(body.index(s) for s in anchors))
        encryption=(RUNTIME/'crates/crypto/circuits/src/encryption.rs').read_text()
        body=encryption[encryption.index('pub fn encrypt('):encryption.index('pub(crate) fn secret')]
        self.assertIn('ephemeral: [Scalar; 4]',body);self.assertIn('ownership_randomness: [Scalar; 2]',body)
        self.assertIn('for r in &ephemeral',body)
        self.assertIn('*r != Scalar::zero() && *r < Scalar::from_limbs(scalar::ORDER)',body)
        self.assertLess(body.index('for r in &ephemeral'),body.index('let epks ='))
        self.assertEqual(body.count('audit::encrypt('),2)
        self.assertEqual(body.count(')?\n            .published'),2)
        statement=(RUNTIME/'crates/crypto/circuits/src/transfer.rs').read_text()
        body=statement[statement.index('pub fn statement('):statement.index('/// Returns the sole public')]
        self.assertNotIn('encryption::encrypt(',body);self.assertNotIn('recovery::encrypt(',body)

    def test_sdk_replacement_retry_and_key_admission_are_distinct(self):
        recovery=(RUNTIME/'crates/core/component/shielded-pool/src/recovery_capsule.rs').read_text()
        opening=recovery[recovery.index('fn derive_opening('):recovery.index('fn derive_salt(')]
        self.assertRegex(opening,r'if r == Fr::from\(0u64\)\s*\{\s*r = Fr::from\(1u64\);')
        self.assertNotIn('loop',opening)
        body=recovery[recovery.index('pub fn encrypt('):recovery.index('pub fn commitment(')]
        anchors=['"recovery payload_key must be nonidentity"','let opening = derive_opening(rseed)',
                 '"zero recovery randomizer"','let epk =','capsule.validate()?','Ok((capsule, opening))']
        self.assertEqual([body.index(s) for s in anchors],sorted(body.index(s) for s in anchors))
        self.assertIn('self.epk != SubgroupPoint::identity()',body)
        rseed=(RUNTIME/'crates/core/component/shielded-pool/src/rseed.rs').read_text()
        body=rseed[rseed.index('pub fn derive_esk('):rseed.index('/// Derive note commitment')]
        self.assertIn('ka::Secret::from_scalar(if scalar == Fr::from(0)',body)
        self.assertIn('Fr::from(1)',body);self.assertNotIn('loop',body)
        transfer=(RUNTIME/'crates/core/component/compliance/src/transfer.rs').read_text()
        sampler=transfer[transfer.index('fn sample_nonzero_scalar('):transfer.index('impl TransferComplianceCiphertext')]
        self.assertIn('loop {',sampler);self.assertIn('if scalar != Fr::from(0u64)',sampler)
        ka=(RUNTIME/'crates/crypto/primitives/src/ka.rs').read_text()
        public=ka[ka.index('pub fn from_point('):ka.index('pub fn point(')]
        self.assertIn('!bool::from(point.is_identity())',public)
        secret=ka[ka.index('pub fn from_scalar('):ka.index('pub fn public(')]
        self.assertIn('!bool::from(scalar.is_zero())',secret)
        address=(RUNTIME/'crates/core/keys/src/address.rs').read_text()
        self.assertIn('diversified_generator.is_identity()',address)

    def test_six_guard_exports_keep_native_callbacks_and_no_desired_row_premises(self):
        source=(REPO/'circuits/ShielddSecurity/NativeEphemeralAdmission.lean').read_text()
        names=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(names),6);self.assertEqual(names,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        for theorem in ('recovery_success','ownership_success','encryption_success','sdkRecovery_success'):
            declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
            self.assertIn('(accepted :',declaration)
            for forbidden in ('(nonidentity','(desired','(satisfied','(inverseEquation','(curve'):
                self.assertNotIn(forbidden,declaration)
        self.assertIn('(ephemeral : Fin 4 → F) (ownership : Fin 2 → F)',source)
        self.assertIn('variable {F : Type} [Field F] [DecidableEq F]',source)
        self.assertIn('{S Payload : Type} [Field S] [DecidableEq S]',source)
        self.assertIn('set_option maxHeartbeats 250000',source)
        self.assertIn('instance validScalarDecidable',source)
        self.assertIn('Fintype.decidableForallFintype',source)
        self.assertNotRegex(source,r'\b(classical|noncomputable)\b')


if __name__=='__main__':unittest.main()
