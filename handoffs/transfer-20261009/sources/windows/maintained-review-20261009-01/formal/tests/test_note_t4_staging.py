"""Fresh note source keeps previously qualified role/fixed capture paths."""
import unittest
from pathlib import Path
from integration.note_t4_staging import diagnostic_note


class NoteT4StagingTests(unittest.TestCase):
    def test_old_authorization_scalar_fixed_code_preserved(self):
        base=Path('tests/fixtures/current-diagnostic-note.rs').read_bytes()
        result=diagnostic_note(base)
        prefix=b'#[cfg(feature = "formal-observer")]\r\npub mod spend_inspection;\r\n' if b'\r\n' in base else b'#[cfg(feature = "formal-observer")]\npub mod spend_inspection;\n'
        result=result.removeprefix(prefix)
        anchor=b'pub fn constrain_spend<'
        self.assertEqual(result[:result.index(anchor)],base[:base.index(anchor)])
        for hook in (b'scalar::inspection::spend_target',b'group::fixed_inspection::spend_scope',
                     b'crate::transfer::inspection::spend(',b'note_inspection::spend()',b'spend_inspection::record('):
            self.assertIn(hook,result)
        with self.assertRaises(ValueError):diagnostic_note(diagnostic_note(base))

    def test_missing_old_hook_refused_before_source_generation(self):
        base=Path('tests/fixtures/current-diagnostic-note.rs').read_bytes()
        for anchor in (b'scalar::inspection::spend_target',b'group::fixed_inspection::spend_scope',
                       b'crate::transfer::inspection::spend('):
            with self.assertRaises(ValueError):diagnostic_note(base.replace(anchor,b'changed'))


if __name__=='__main__':unittest.main()
