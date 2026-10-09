"""EPK hooks must conserve original circuit operation sequence, unlike metadata hashes."""
import unittest
from pathlib import Path
from integration import epk_fixed_observer as observer

ROOT=Path(__file__).parents[1]
P=ROOT/'.work/diagnostics/transfer-implementation-20261002'
GROUP=P/'balance-variable-observer-source-05/before/crates/crypto/circuits/src/group.rs'
RECOVERY=P/'transfer-future-gaps-source-04'

class EpkFixedObserverTests(unittest.TestCase):
    def test_group_old_observers_and_operations_exact(self):
        old=GROUP.read_bytes();new=observer.instrument_group(old).decode()
        # Erase only new cfg blocks. Every old operation/hook remains byte-identical.
        import re
        stripped=re.sub(r'\n[ ]*#\[cfg\(feature = "formal-observer"\)\]\n[ ]*(?:pub mod epk_fixed_inspection;|epk_fixed_inspection::\w+\([^;]*\);)', '',new)
        self.assertEqual(stripped.replace('let epk_fixed_inverse = self.x.inv();','let _ = self.x.inv();').encode(),old)
        with self.assertRaises(ValueError):observer.instrument_group(new.encode())
        with self.assertRaises(ValueError):observer.instrument_group(old.replace(b'let next = add(&result, &selected);',b'let next = altered();').replace(b'fixed_inspection::finish_window',b'changed::finish_window'))
        self.assertEqual(observer.instrument_group(old.replace(b'\n',b'\r\n')),observer.instrument_group(old).replace(b'\n',b'\r\n'))

    def test_recovery_same_generator_scalar_output_operations(self):
        old=b'let randomizer = var(&witness.randomizer);\n    let bits = scalar::canonical_bits(ctx, &randomizer);\n    let computed_epk = group::generator().multiply_fixed(&bits);\n    computed_epk.assert_equal(&out.epk);\n    let epk_inverse = out.epk.x.inv();\n'
        new=observer.instrument_recovery(old).decode()
        before='    let epk_generator = group::generator();\n    #[cfg(feature = "formal-observer")]\n    let epk_fixed_scope = group::epk_fixed_inspection::scope(\n        group::epk_fixed_inspection::Lane::Recovery, &epk_generator, &randomizer, &bits, &out.epk);\n    let computed_epk = epk_generator.multiply_fixed(&bits);'
        stripped=new.replace(before,'    let computed_epk = group::generator().multiply_fixed(&bits);')
        stripped=stripped.replace('\n    #[cfg(feature = "formal-observer")]\n    group::epk_fixed_inspection::inverse(&epk_inverse);\n    #[cfg(feature = "formal-observer")]\n    drop(epk_fixed_scope);','')
        self.assertEqual(stripped.encode(),old)
        self.assertEqual(new.count('group::generator()'),1)
        self.assertEqual(new.count('var(&witness.randomizer)'),1)
        with self.assertRaises(ValueError):observer.instrument_recovery(new.encode())

    def test_encryption_four_roles_same_scalar_operations(self):
        old=b'    let generator = group::generator();\n    for i in 0..4 {\n        let bits = scalar::canonical_bits(ctx, &var(&w.ephemeral[i]));\n        existing_bits_observer(&bits);\n        generator.multiply_fixed(&bits).assert_equal(epks[i]);\n        epks[i].assert_non_identity();\n    }\n'
        new=observer.instrument_encryption(old).decode()
        import re
        stripped=re.sub(r'        #\[cfg\(feature = "formal-observer"\)\]\n        let epk_fixed_scope =[^;]*;\n','',new)
        stripped=stripped.replace('\n        #[cfg(feature = "formal-observer")]\n        drop(epk_fixed_scope);','')
        stripped=stripped.replace('        let epk_randomizer = var(&w.ephemeral[i]);\n        let bits = scalar::canonical_bits(ctx, &epk_randomizer);','        let bits = scalar::canonical_bits(ctx, &var(&w.ephemeral[i]));')
        self.assertEqual(stripped.encode(),old)
        with self.assertRaises(ValueError):observer.instrument_encryption(new.encode())

    def test_bounded_capture_path_real_lowerer_and_native_tests(self):
        runtime=(ROOT/'integration/observers/epk_fixed.rs').read_text()
        catalogue=(ROOT/'integration/observers/epk_fixed_catalogue.rs').read_text()
        self.assertNotIn('Var::witness',runtime.split('#[cfg(test)]')[0]);self.assertNotIn('.value(',runtime)
        self.assertIn('state.calls+=1',runtime);self.assertIn('index!=state.slot',runtime)
        self.assertIn('s.calls==s.lane.slots()',runtime)
        self.assertIn('quotient[4..]!=points[2]',runtime)
        self.assertIn('last.table[3]!=native(base)',runtime)
        self.assertIn('8,selections.iter().map(Vec::as_slice)',catalogue)
        self.assertLess(catalogue.index('nodes.push((node,multiply,left,right))'),catalogue.index('if boundaries.contains'))
        self.assertIn('selected.len()<=4096',catalogue)
        self.assertIn('visited.len()<=8192',catalogue)
        self.assertEqual([min(16,126-i) for i in range(0,126,16)],[16]*7+[14])
        self.assertEqual(runtime.count('#[test]'),7)
        self.assertIn('scope_id(all.reports.len())==Some((r.lane,r.slot))',runtime)
        self.assertIn('s.reports.len()==6',runtime)
        self.assertIn('48,selections.iter().map(Vec::as_slice)',catalogue)
        self.assertIn('use commonware_math::algebra::Field;',runtime.split('#[cfg(test)]')[1])
        self.assertNotIn('Var::constant(',runtime.split('#[cfg(test)]')[1])

    def test_existing_qualifier_flags_follow_strict_repeat_pages(self):
        old=b"""fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
}
fn qualified() {
        Some(\"shieldd-transfer-note-spend-v1\") |
            pending[\"repeated_observations_equal\"] = json!(true);
}
fn old_mode() {}
"""
        fragment=(ROOT/'integration/observers/epk_fixed_export.rs').read_bytes()
        new=observer.instrument_exporter(old,fragment).decode()
        self.assertIn('fn old_mode() {}',new)
        self.assertLess(new.index('qualify_epk_fixed_pages(first,repeated,&pending)?;'),new.index('pending["repeated_observations_equal"] = json!(true);'))
        self.assertIn('count==8 && copy==200692',new)
        self.assertIn('shape["source_public"]==json!([[1,22734]])',new)
        self.assertIn('shape["source_blocks"]==json!([[[1,6]]])',new)
        self.assertIn('16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236',new)
        self.assertIn('bytes==read_epk_fixed_page(repeated,ordinal)?',new)
        self.assertIn('epk-all-fixed-pages-spool',new)
        self.assertIn('scopes.len()==6 && pages.len()==48',new)
        self.assertLess(new.index('qualify_epk_all_fixed_pages(first,repeated,&pending)?;'),new.index('pending["repeated_observations_equal"] = json!(true);'))
        self.assertIn('"ordinary_full_ordered_rows_equal":false',new)
        with self.assertRaises(ValueError):observer.instrument_exporter(new.encode(),fragment)
        with self.assertRaises(ValueError):observer.instrument_exporter(old,fragment.replace(b'fn qualify_epk_fixed_page(',b'fn omitted('))
