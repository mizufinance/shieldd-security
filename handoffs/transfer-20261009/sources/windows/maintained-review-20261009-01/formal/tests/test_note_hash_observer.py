"""Pure fresh-stage recipe controls; no runtime build or capture qualification."""
import unittest
from pathlib import Path
from integration import note_hash_observer as hooks


class NoteHashObserverTests(unittest.TestCase):
    def test_scope_is_in_existing_spend_and_is_repeat_safe(self):
        source=Path('tests/fixtures/current-note-spend.rs').read_bytes()
        result=hooks.instrument_note(source)
        self.assertEqual(result.count(b'note_inspection::spend()'),1)
        self.assertEqual(result.replace(b'\n    #[cfg(feature = "formal-observer")]\n    let _note_hash_scope = crate::hash::note_inspection::spend();',b''),source)
        with self.assertRaisesRegex(ValueError,'drift/duplicate'):hooks.instrument_note(result)

    def test_hash_sink_preserves_existing_sink_and_arithmetic(self):
        source=b'''pub fn circuit() {
            let call = inspection::start(domain, inputs);
            let observe = |block, after, state| {
                inspection::state(&call, block, after, state);
            };
            let output = self.wide.hash_observed(domain, inputs, lift, &observe);
            inspection::finish(call, &output);
            return output;
}'''
        result=hooks.instrument_hash(source)
        self.assertIn(b'self.wide.hash_observed(domain, inputs, lift, &observe)',result)
        self.assertEqual(result.count(b'inspection::state(&call,'),1)
        self.assertEqual(result.count(b'note_inspection::state(&note_call,'),1)
        with self.assertRaisesRegex(ValueError,'already activated'):hooks.instrument_hash(result)
        with self.assertRaisesRegex(ValueError,'anchor drift'):hooks.instrument_hash(source.replace(b'let call =',b'let changed ='))

    def test_line_endings_and_existing_qualifier_dispatch(self):
        source=Path('tests/fixtures/current-note-spend.rs').read_bytes().replace(b'\n',b'\r\n')
        result=hooks.instrument_note(source)
        self.assertNotIn(b'\n',result.replace(b'\r\n',b''))
        exporter=b'''fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    match schema {
        Some("shieldd-transfer-note-spend-v1") => { qualify_full_rows_and_repeat(); }
    }
}'''
        result=hooks.instrument_exporter(exporter,b'fn capture_note_hash() {}')
        self.assertIn(b'Some("shieldd-transfer-note-hash-block-v1")',result)
        self.assertIn(b'qualify_full_rows_and_repeat();',result)
        with self.assertRaises(ValueError):hooks.instrument_exporter(result,b'fn capture_note_hash() {}')


if __name__=='__main__':unittest.main()
