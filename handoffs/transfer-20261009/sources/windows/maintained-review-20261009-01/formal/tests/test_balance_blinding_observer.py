"""Small source conservation tests. All native Rust tests/captures are UNRUN."""
import re,unittest
from pathlib import Path
from integration import balance_blinding_observer as observer

ROOT=Path(__file__).parents[1];P=ROOT/'.work/diagnostics/transfer-implementation-20261002'


class BlindingObserverTests(unittest.TestCase):
    def test_additive_group_preserves_epk_and_variable_hooks_exactly(self):
        old=(P/'epk-fixed-observer-source-05/balance-sibling-overlay/crates/crypto/circuits/src/group.rs').read_bytes()
        new=observer.instrument_group(old).decode()
        erased=re.sub(r'\n[ ]*#\[cfg\(feature = "formal-observer"\)\]\n[ ]*(?:pub mod balance_blinding_fixed_inspection;|balance_blinding_fixed_inspection::\w+\([^;]*\);)','',new)
        self.assertEqual(erased.encode(),old)
        self.assertEqual(observer.instrument_group(old.replace(b'\n',b'\r\n')),new.replace('\n','\r\n').encode())
        self.assertIn('epk_fixed_inspection::finish_window',new);self.assertIn('balance_variable_inspection',new)
        with self.assertRaises(ValueError):observer.instrument_group(new.encode())
        with self.assertRaises(ValueError):observer.instrument_group(old.replace(b'fixed_inspection::begin_window(_index);',b'changed();'))

    def test_blinding_same_canonical_call_multiply_order_and_zero_domain(self):
        old=(P/'balance-variable-observer-source-05/overlay/crates/crypto/circuits/src/balance.rs').read_bytes()
        new=observer.instrument_balance(old).decode()
        replacement='''    let blinding_bits = scalar::canonical_bits(ctx, blinding);
    #[cfg(feature = "formal-observer")]
    let balance_blinding_scope = crate::group::balance_blinding_fixed_inspection::scope(
        &generators.blinding, blinding, &blinding_bits);
    let blinded = generators.blinding.multiply_fixed(&blinding_bits);
    #[cfg(feature = "formal-observer")]
    drop(balance_blinding_scope);'''
        restored=new.replace('\r\n','\n').replace(replacement,'    let blinded = generators\n        .blinding\n        .multiply_fixed(&scalar::canonical_bits(ctx, blinding));')
        self.assertEqual(restored.replace('\n','\r\n').encode() if b'\r\n' in old else restored.encode(),old)
        self.assertEqual(new.count('scalar::canonical_bits(ctx, blinding)'),old.decode().count('scalar::canonical_bits(ctx, blinding)'))
        self.assertLess(new.index('let blinding_bits'),new.index('let blinded = generators.blinding'))
        self.assertNotIn('assert_non_identity',replacement);self.assertNotIn('.inv()',replacement)
        with self.assertRaises(ValueError):observer.instrument_balance(new.encode())

    def test_complete_append_preserves_old_modes_and_qualifies_before_flags(self):
        old=(P/'epk-fixed-observer-source-05/balance-sibling-overlay/crates/crypto/circuits/examples/transfer-ownership-inspection.rs').read_bytes()
        fragment=(ROOT/'integration/observers/balance_blinding_fixed_export.rs').read_bytes()
        new=observer.instrument_exporter(old,fragment).decode()
        self.assertIn('capture_epk_all_fixed_pages(&args[1])',new);self.assertIn('capture_balance_variable_pages(&args[1])',new)
        self.assertLess(new.index('qualify_balance_blinding_fixed_pages(first,repeated,&pending)?;'),new.index('pending["repeated_observations_equal"] = json!(true);'))
        self.assertIn('bytes==read_balance_blinding_fixed_page(repeated,ordinal)?',new)
        self.assertIn('shape["source_public"]==json!([[1,22734]])',new)
        self.assertIn('shape["source_blocks"]==json!([[[1,6]]])',new)
        self.assertNotIn('"inverse"',fragment.decode());self.assertNotIn('"lane"',fragment.decode())
        self.assertIn('"ordinary_full_ordered_rows_equal":false',fragment.decode())
        with self.assertRaises(ValueError):observer.instrument_exporter(new.encode(),fragment)

    def test_bounded_one_compile_source_and_native_lifecycle_tests(self):
        runtime=(ROOT/'integration/observers/balance_blinding_fixed.rs').read_text()
        catalogue=(ROOT/'integration/observers/balance_blinding_fixed_catalogue.rs').read_text()
        self.assertEqual(runtime.count('#[test]'),4);self.assertIn('shieldd_sdk_crypto::generators::VALUE_BLINDING',runtime)
        self.assertIn('actual_value_blinding_zero_trace_is_complete_and_satisfied',runtime)
        self.assertNotIn('Var::witness',runtime.split('#[cfg(test)]')[0])
        self.assertNotIn('inverse',runtime.split('#[cfg(test)]')[0]);self.assertIn('state.calls!=1',runtime)
        self.assertIn('8,selections.iter().map(Vec::as_slice)',catalogue)
        self.assertIn('selected.len()<=4096',catalogue);self.assertIn('visited.len()<=8192',catalogue)
        self.assertLess(catalogue.index('nodes.push'),catalogue.index('if boundaries.contains'))

