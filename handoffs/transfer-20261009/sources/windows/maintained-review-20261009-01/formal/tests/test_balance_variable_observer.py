"""Bounded future hook preserves reviewed circuit operations and odd pairing."""
from pathlib import Path
import unittest
from integration import balance_variable_observer as observer

GROUP=b'''#[cfg(feature = "formal-observer")]
pub mod ownership_inspection;
fn quotients() {
    #[cfg(feature = "formal-observer")]
    fixed_inspection::quotient([&observed_numerators.0, &observed_numerators.1,
        &dx, &dy, &output.x, &output.y]);
}
fn affine_variable<'a>(base: &Point<V<'a>>, bits: &[BoolVar<'a, Scalar>]) -> Point<V<'a>> {
    let twice = double(base);
    let triple = add(&twice, base);
    let mut result = Point::identity();
    for pair in bits.chunks(2).rev() {
        let first = double(&result);
        let second = double(&first);
        let selected = select(base, &twice, &triple, pair);
        let next = add(&second, &selected);
        result = next;
    }
    result
}
fn affine_fixed<'a>() {}
'''
BALANCE=b'''fn constrain() {
    let magnitude_bits = signed_bits(ctx, &(input - &output), &negative, &magnitude);
    let mut value = generator.multiply_bits(&magnitude_bits);
    value.x = negative.select(&(-value.x.clone()), &value.x);
    value.add(&blinded, &d)
}
'''

class BalanceVariableObserverTests(unittest.TestCase):
    def test_existing_exporter_fullrow_qualification_and_modes_preserved(self):
        original=b'''fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
}
fn qualified_metadata() {
        Some("shieldd-transfer-note-spend-v1") |
            pending["repeated_observations_equal"] = json!(true);
}
fn existing_mode() {}
'''
        root=Path(__file__).parents[1]/'integration/observers'
        fragment=(root/'balance_variable_export.rs').read_bytes()+b'\n'+(root/'balance_variable_pages_export.rs').read_bytes()
        generated=observer.instrument_exporter(original,fragment).decode()
        self.assertIn('fn existing_mode() {}',generated)
        self.assertLess(generated.index('qualify_balance_variable(&pending)?;'),generated.index('pending["repeated_observations_equal"] = json!(true);'))
        self.assertIn('"ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false',generated)
        self.assertIn('balance variable role missing selected LC',generated)
        self.assertIn('balance-variable-pages-spool',generated)
        self.assertLess(generated.index('qualify_balance_variable_pages(first,repeated,&pending)?;'),generated.index('pending["repeated_observations_equal"] = json!(true);'))
        with self.assertRaises(ValueError):observer.instrument_exporter(original,(root/'balance_variable_export.rs').read_bytes())
        with self.assertRaises(ValueError):observer.instrument_exporter(generated.encode(),fragment)
        with self.assertRaises(ValueError):observer.instrument_exporter(original.replace(b'note-spend-v1',b'changed-v1'),fragment)
        catalogue=observer.instrument_catalogue(b'fn existing_catalogue() {}\n')
        self.assertTrue(catalogue.startswith(b'fn existing_catalogue() {}\n'))
        with self.assertRaises(ValueError):observer.instrument_catalogue(catalogue)

    def test_original_operations_and_other_observers_survive_exactly(self):
        group=observer.instrument_group(GROUP).decode()
        additions=[
            '\n#[cfg(feature = "formal-observer")]\npub mod balance_variable_inspection;',
            '\n    #[cfg(feature = "formal-observer")]\n    balance_variable_inspection::quotient([&observed_numerators.0, &observed_numerators.1,\n        &dx, &dy, &output.x, &output.y]);',
            '    #[cfg(feature = "formal-observer")]\n    balance_variable_inspection::begin_loop(base, bits, &twice, &triple);\n    #[cfg(feature = "formal-observer")]\n    let mut balance_window_index = 0;\n',
            '\n        #[cfg(feature = "formal-observer")]\n        balance_variable_inspection::begin_window(balance_window_index);',
            '        #[cfg(feature = "formal-observer")]\n        {\n            balance_variable_inspection::finish_window(balance_window_index, pair,\n                [&result, &first, &second, &selected, &next]);\n            balance_window_index += 1;\n        }\n',
            '    #[cfg(feature = "formal-observer")]\n    balance_variable_inspection::finish_loop(&result);\n']
        for addition in additions:
            self.assertEqual(group.count(addition),1);group=group.replace(addition,'')
        self.assertEqual(group.encode(),GROUP)
        balance=observer.instrument_balance(BALANCE).decode()
        before='    #[cfg(feature = "formal-observer")]\n    let balance_variable_scope = crate::group::balance_variable_inspection::scope(\n        &generator, &negative, &magnitude, &magnitude_bits);\n'
        after='\n    #[cfg(feature = "formal-observer")]\n    drop(balance_variable_scope);'
        self.assertEqual(balance.replace(before,'').replace(after,'').encode(),BALANCE)
        self.assertEqual(observer.instrument_group(GROUP.replace(b'\n',b'\r\n')),observer.instrument_group(GROUP).replace(b'\n',b'\r\n'))

    def test_source_drift_duplicate_and_finite_pairing_refusal(self):
        for data in [GROUP+GROUP,GROUP.replace(b'let first = double(&result);',b'let changed = double(&result);')]:
            with self.assertRaises(ValueError):observer.instrument_group(data)
        with self.assertRaises(ValueError):observer.instrument_group(observer.instrument_group(GROUP))
        with self.assertRaises(ValueError):observer.instrument_balance(BALANCE.replace(b'multiply_bits',b'multiply'))
        with self.assertRaises(ValueError):observer.instrument_balance(observer.instrument_balance(BALANCE))
        source=(Path(__file__).parents[1]/'integration/observers/balance_variable.rs').read_text()
        self.assertIn('state.invalid || state.report.is_some()',source)
        self.assertIn('state.quotient_count != 197',source)
        self.assertIn('report.windows.len() >= state.count',source)
        self.assertIn('if index == 0 { Observed::Native(Scalar::zero()) }',source)
        self.assertIn('pair.get(1).map',source)
        self.assertIn('report.precompute_quotients[0][4..] == report.twice',source)
        self.assertNotIn('Var::witness',source)
        self.assertNotIn('.value(',source)
        catalogue=(Path(__file__).parents[1]/'integration/observers/balance_variable_catalogue.rs').read_text()
        self.assertLess(catalogue.index('nodes.push((node,multiply,left,right))'),catalogue.index('if boundaries.contains(&index) { continue; }'))
        self.assertLess(catalogue.index('if boundaries.contains(&index) { continue; }'),catalogue.index('pending.extend([left,right])'))
        pairs=[([128] if index==0 else [128-2*index,129-2*index]) for index in range(65)]
        self.assertEqual(pairs[0],[128]);self.assertEqual(pairs[-1],[0,1])
        self.assertEqual(sorted(bit for pair in pairs for bit in pair),list(range(129)))

    def test_five_page_lifecycle_bounds_and_same_lowerer(self):
        root=Path(__file__).parents[1]/'integration/observers'
        catalogue=(root/'balance_variable_catalogue.rs').read_text()
        exporter=(root/'balance_variable_pages_export.rs').read_text()
        runtime=(root/'balance_variable.rs').read_text()
        self.assertIn('start: 0, count: 65',runtime)
        self.assertIn('self.windows.len() == 65',runtime)
        self.assertIn('(1..=16).contains(&count)',runtime)
        self.assertIn('[0,16,32,48,64]',catalogue)
        self.assertIn('&c,&layout,5,selections.iter().map(Vec::as_slice)',catalogue)
        self.assertIn('expected.as_slice()==selected',catalogue)
        self.assertNotIn('compile_nodes()',catalogue)
        self.assertIn('count==5 && copy==200692',exporter)
        self.assertLess(exporter.index('count==5 && copy==200692'),exporter.index('"shieldd-transfer-balance-variable-pages-v1"'))
        self.assertIn('bytes==read_balance_variable_page(repeated,ordinal)?',exporter)
        self.assertIn('descriptor["blake3"]==packet_blake3(&bytes)',exporter)
        self.assertIn('qualify_balance_variable(&page)?',exporter)

if __name__=='__main__':unittest.main()
