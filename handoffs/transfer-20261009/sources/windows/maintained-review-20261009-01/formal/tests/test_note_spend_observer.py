"""Pure fresh-stage hook checks against the pinned current runtime fragment."""
from pathlib import Path
import unittest
from integration.note_spend_observer import instrument_note, instrument_catalogue, instrument_exporter

FIXTURE = Path(__file__).parent/'fixtures/current-note-spend.rs'


class NoteSpendObserverTests(unittest.TestCase):
    def test_current_hooks_preserve_unowned_source_and_capture_named_existing_products(self):
        original=FIXTURE.read_bytes(); prefix=b'// authorization sentinel\n'; suffix=b'\n// output sentinel\n'
        result=instrument_note(prefix+original+suffix)
        self.assertIn(prefix,result);self.assertTrue(result.endswith(suffix))
        self.assertEqual(result.count(b'spend_inspection::record('),2)
        self.assertEqual(result.count(b'spend_inspection::optional('),1)
        self.assertIn(b'commitment.clone(), &path, &positions',result)
        self.assertIn(b'let selector_product = dummy.var().clone() * &selector_delta;',result)
        self.assertIn(b'let amount_product = dummy.var().clone() * &note.amount;',result)
        self.assertNotIn(b'history',result)

    def test_repeat_and_changed_arithmetic_anchor_are_refused(self):
        source=FIXTURE.read_bytes()
        with self.assertRaises(ValueError):instrument_note(instrument_note(source))
        for change in (source.replace(b'128);',b'127);'),
                       source.replace(b'anchor - &shared.anchor',b'anchor + &shared.anchor'),
                       source.replace(b'            dummy\n                .select',b'            real\n                .select')):
            with self.subTest(change=change),self.assertRaises(ValueError):instrument_note(change)

    def test_portable_line_endings_and_catalogue_repeat_refusal(self):
        source=FIXTURE.read_bytes(); lf=instrument_note(source)
        self.assertEqual(instrument_note(source.replace(b'\n',b'\r\n')),lf.replace(b'\n',b'\r\n'))
        with self.assertRaises(ValueError):instrument_note(source.replace(b'\n',b'\r\n',1))
        out=instrument_catalogue(b'// catalogue sentinel\n')
        self.assertTrue(out.startswith(b'// catalogue sentinel\n'))
        with self.assertRaises(ValueError):instrument_catalogue(out)

    def test_existing_spool_path_gets_one_pending_mode_and_same_full_parity_qualifier(self):
        root=Path(__file__).resolve().parents[1]
        original=(root/'tests/fixtures/current-transfer-ownership-inspection.rs').read_bytes()
        fragment=(root/'integration/observers/note_spend_export.rs').read_bytes()
        result=instrument_exporter(original,fragment)
        self.assertEqual(result.count(b'args[0] == "note-spend-spool"'),1)
        self.assertIn(b'Some("shieldd-transfer-note-spend-v1") => {',result)
        self.assertIn(b'"ordinary_full_ordered_rows_equal":false',result)
        self.assertIn(b'compare_framed_rows(&paths[0], path, 200770, 262144)',result)
        self.assertIn(b'pending == repeat',result)
        with self.assertRaises(ValueError):instrument_exporter(result,fragment)
        with self.assertRaises(ValueError):instrument_exporter(original.replace(b'fixed-spend-v1',b'fixed-spend-v9'),fragment)


if __name__=='__main__':unittest.main()
