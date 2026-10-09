"""Future recovery source operation identity and strict bounded lifecycle shape."""
import unittest
from pathlib import Path
from integration import recovery_capsule_observer as observer


class RecoveryCapsuleObserverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original=Path('tests/fixtures/current-recovery.rs').read_bytes()
        cls.group=Path('tests/fixtures/current-recovery-group.rs').read_bytes()

    def test_existing_constructor_and_plaintext_operations_are_exactly_preserved(self):
        result=observer.instrument_recovery(self.original,self.group).decode().replace('\r\n','\n')
        restored=result.removeprefix('#[cfg(feature = "formal-observer")]\npub mod capsule_inspection;\n')
        for addition in (
            '    #[cfg(feature = "formal-observer")]\n    let _capsule_scope = capsule_inspection::scope();\n',
            '    #[cfg(feature = "formal-observer")]\n    capsule_inspection::core(payload_key, amount, blinding, &randomizer, &bits,\n        &seed, &out, &computed_epk, &shared, &secret, &computed_c2, &epk_inverse);\n',
            '    #[cfg(feature = "formal-observer")]\n    capsule_inspection::plaintext(amount, blinding, capsule, seed,\n        &computed_confirmation, &amount_stream, &computed_amount,\n        &blinding_stream, &computed_blinding, &epk_inverse);\n'):
            self.assertEqual(restored.count(addition),1)
            restored=restored.replace(addition,'')
        restored=restored.replace('    let randomizer = var(&witness.randomizer);\n    let bits = scalar::canonical_bits(ctx, &randomizer);\n    let computed_epk = group::generator().multiply_fixed(&bits);\n    computed_epk.assert_equal(&out.epk);',
            '    let bits = scalar::canonical_bits(ctx, &var(&witness.randomizer));\n    group::generator()\n        .multiply_fixed(&bits)\n        .assert_equal(&out.epk);')
        restored=restored.replace('    let secret = encryption::secret(params, &shared);\n    let computed_c2 = seed.clone() + &secret;\n    computed_c2.assert_eq(&out.c2);',
            '    (seed.clone() + &encryption::secret(params, &shared)).assert_eq(&out.c2);')
        restored=restored.replace('    let computed_confirmation = params\n        .circuit(', '    params\n        .circuit(')
        restored=restored.replace('        );\n    computed_confirmation.assert_eq(&capsule.confirmation);\n    let amount_stream = encryption::stream(params, seed, 0);\n    let computed_amount = amount.clone() + &amount_stream;\n    computed_amount.assert_eq(&capsule.encrypted_amount);\n    let blinding_stream = encryption::stream(params, seed, 1);\n    let computed_blinding = blinding.clone() + &blinding_stream;\n    computed_blinding.assert_eq(&capsule.encrypted_blinding);',
            '        )\n        .assert_eq(&capsule.confirmation);\n    (amount.clone() + &encryption::stream(params, seed, 0)).assert_eq(&capsule.encrypted_amount);\n    (blinding.clone() + &encryption::stream(params, seed, 1))\n        .assert_eq(&capsule.encrypted_blinding);')
        self.assertEqual(restored.count('let epk_inverse ='),2)
        restored=restored.replace('let epk_inverse = out.epk.x.inv();','out.epk.assert_non_identity();')
        restored=restored.replace('let epk_inverse = capsule.epk.x.inv();','capsule.epk.assert_non_identity();')
        self.assertIn('use commonware_math::algebra::{Additive, Field};',restored)
        restored=restored.replace('use commonware_math::algebra::{Additive, Field};','use commonware_math::algebra::Additive;')
        self.assertEqual(restored,self.original.decode().replace('\r\n','\n'))
        for operation in ('Var::witness(', 'scalar::canonical_bits(', '.multiply_fixed(', '.multiply_bits(',
                          'encryption::secret(params,', 'encryption::stream(params,', '.circuit('):
            self.assertEqual(result.count(operation),restored.count(operation))

    def test_fresh_source_refuses_duplicate_drift_and_mixed_line_endings(self):
        with self.assertRaises(ValueError):observer.instrument_recovery(observer.instrument_recovery(self.original,self.group),self.group)
        for old in (b'&var(&witness.randomizer)',b'.assert_eq(&out.c2);',b'.assert_eq(&capsule.commitment);'):
            with self.assertRaises(ValueError):observer.instrument_recovery(self.original.replace(old,b'/* changed */'),self.group)
        with self.assertRaisesRegex(ValueError,'nonidentity operation'):
            observer.instrument_recovery(self.original,self.group.replace(b'let _ = self.x.inv();',b'let _ = self.y.inv();'))
        crlf=self.original.replace(b'\r\n',b'\n').replace(b'\n',b'\r\n')
        result=observer.instrument_recovery(crlf,self.group)
        self.assertNotIn(b'\n',result.replace(b'\r\n',b''))
        with self.assertRaises(ValueError):observer.instrument_recovery(crlf+b'\n',self.group)

    def test_companion_has_fixed_capsule_count_bits_and_source_link_refusals(self):
        source=Path('integration/observers/recovery_capsule.rs').read_text()
        for check in ('bits.len()!=252','s.reports.len()==2','handles.len()<=1024','core.amount!=observed(amount)',
            'core.blinding!=observed(blinding)','core.seed!=observed(seed)','core.commitment!=observed(&capsule.commitment)',
            's.pending.is_some()','s.reports.len()!=self.before+1','s.active || s.taken','s.invalid=true'):
            self.assertIn(check,source)
        for operation in ('Var::witness(', 'Var::native(', '.circuit(', '.multiply_bits(', '.multiply_fixed('):
            self.assertNotIn(operation,source)
        self.assertIn('Input release plaintext calls outside constrain are deliberately ignored',source)
        self.assertIn('pub fn take()->anyhow::Result<[Report;2]>',source)
        self.assertEqual(source.count('#[test]'),2)

    def test_retained_inverse_import_repair_changes_only_trait_scope(self):
        expanded=observer.instrument_recovery(self.original,self.group)
        old=expanded.replace(b'use commonware_math::algebra::{Additive, Field};',b'use commonware_math::algebra::Additive;')
        self.assertEqual(observer.import_existing_inverse_field(old),expanded)
        self.assertEqual(observer.import_existing_inverse_field(old).count(b'.x.inv();'),2)
        with self.assertRaises(ValueError):observer.import_existing_inverse_field(expanded)
        with self.assertRaises(ValueError):observer.import_existing_inverse_field(old.replace(b'out.epk.x.inv()',b'out.epk.y.inv()'))


if __name__=='__main__':unittest.main()
