"""Source hook preservation and refusal; Rust semantic tests run only at root."""
import unittest
from pathlib import Path
from integration import note_output_observer as observer,note_spend_observer as spend


class NoteOutputObserverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.original=Path('tests/fixtures/current-diagnostic-note.rs').read_bytes()
    def test_existing_range_inverse_hash_and_capsule_operations_keep_exact_order(self):
        result=observer.instrument_note(self.original).decode().replace('\r\n','\n')
        start=result.index('pub fn constrain_output<');body=result[start:result.index('\n#[cfg(test)]',start)]
        anchors=['let note = w.note.witness(ctx);','decompose(ctx, &note.amount, 128)',
            'note.amount.inv()','Var::witness(ctx, |_| w.commitment.clone())',
            'params.circuit(NOTE, &note.fields(asset, address))','computed_commitment.assert_eq(&commitment)',
            'let capsule = recovery::constrain(','capsule.commitment.assert_eq(&note.recovery)',
            'output_inspection::record','    Output {']
        offsets=[body.index(anchor) for anchor in anchors];self.assertEqual(offsets,sorted(offsets))
        self.assertTrue(all(body.count(anchor)==1 for anchor in anchors))
        expected=self.original.decode().replace('\r\n','\n')
        original_start=expected.index('pub fn constrain_output<')
        before=result[:start].removeprefix('#[cfg(feature = "formal-observer")]\npub mod output_inspection;\n')
        self.assertEqual(before,expected[:original_start])
        self.assertEqual(result[result.index('\n#[cfg(test)]',start):],expected[expected.index('\n#[cfg(test)]',original_start):])
        self.assertIn('receiver_inverse.as_ref()',body)
        self.assertNotIn('Var::native(',body);self.assertNotIn('Var::one(',body)

    def test_fresh_recipe_composes_with_spend_without_mutating_its_hooks(self):
        spend_source=spend.instrument_note(self.original)
        result=observer.instrument_note(spend_source)
        start=spend_source.index(b'pub fn constrain_spend<');end=spend_source.index(b'pub struct OutputWitness')
        self.assertIn(spend_source[start:end],result)
        self.assertEqual(result.count(b'pub mod spend_inspection;'),1)
        self.assertEqual(result.count(b'pub mod output_inspection;'),1)
        crlf=observer.instrument_note(self.original.replace(b'\r\n',b'\n').replace(b'\n',b'\r\n'))
        self.assertNotIn(b'\n',crlf.replace(b'\r\n',b''))

    def test_duplicate_source_drift_and_truncated_inverse_refuse(self):
        for source in (observer.instrument_note(self.original),
            self.original.replace(b'let _ = note.amount.inv();',b'let _ = note.amount.clone();'),
            self.original.replace(b'.assert_eq(&commitment);',b'.assert_eq(&note.recovery);'),
            self.original.replace(b'capsule.commitment.assert_eq(&note.recovery);',b''),
            self.original+b'\r\n'):
            with self.assertRaises(ValueError):observer.instrument_note(source)

    def test_fresh_exporter_retains_full_ordered_qualifier_and_pending_flags(self):
        base=Path('integration/src/bin/transfer-ownership-inspection.rs').read_bytes()
        fragment=Path('integration/observers/note_output_export.rs').read_bytes()
        result=observer.instrument_exporter(base,fragment)
        self.assertEqual(result.count(b'compare_framed_rows(&paths[0], path, 200770, 262144)?;'),1)
        self.assertIn(b'pending["repeated_observations_equal"] = json!(true);',result)
        self.assertIn(b'"ordinary_full_ordered_rows_equal":false',fragment)
        self.assertIn(b'"repeated_observations_equal":false',fragment)
        self.assertIn(b'Some("shieldd-transfer-note-output-v1")',result)
        self.assertEqual(result.count(b'fn capture_note_outputs('),1)
        with self.assertRaises(ValueError):observer.instrument_exporter(result,fragment)
        catalogue=observer.instrument_catalogue(b'// fresh catalogue\n')
        with self.assertRaises(ValueError):observer.instrument_catalogue(catalogue)

    def test_output_hash_scopes_keep_spend_and_output_operations_and_refuse_repeat(self):
        base=observer.instrument_note(spend.instrument_note(self.original))
        scoped=observer.instrument_output_hash_note(base)
        addition=b'    #[cfg(feature = "formal-observer")]\n    let _output_hash_scope = output_hash_inspection::output();'
        normalized=lambda data:data.replace(b'\r\n',b'\n')
        self.assertEqual(normalized(scoped).removeprefix(b'#[cfg(feature = "formal-observer")]\npub mod output_hash_inspection;\n').replace(b'\n'+addition,b''),normalized(base))
        with self.assertRaises(ValueError):observer.instrument_output_hash_note(scoped)
        with self.assertRaises(ValueError):observer.instrument_output_hash_note(self.original)
        hash_source=(b'            let note_call = note_inspection::start(domain, inputs);\n'
            b'                note_inspection::state(&note_call, block, after, state);\n'
            b'            note_inspection::finish(note_call, &output);\n')
        instrumented=observer.instrument_output_hash_hash(hash_source)
        for call in ('start(domain, inputs)','state(&output_call, block, after, state)','finish(output_call, &output)'):
            self.assertIn(call.encode(),instrumented)
        removed=normalized(instrumented)
        for line in removed.splitlines():
            if b'output_hash_inspection::' in line:removed=removed.replace(line+b'\n',b'')
        self.assertEqual(removed,normalized(hash_source))
        with self.assertRaises(ValueError):observer.instrument_output_hash_hash(instrumented)
        with self.assertRaises(ValueError):observer.instrument_output_hash_hash(hash_source.replace(b'note_inspection::finish(note_call, &output);',b''))

    def test_record_uses_one_context_lifetime_for_note_field_composition(self):
        source=Path('integration/observers/note_output.rs').read_text()
        start=source.index("pub(crate) fn record<'ctx>(");end=source.index(') {',start)
        signature=source[start:end]
        self.assertIn("Note<Var<'ctx, Scalar>>",signature)
        self.assertIn("Address<Var<'ctx, Scalar>>",signature)
        self.assertIn("asset: &Var<'ctx, Scalar>",signature)
        self.assertNotIn("<'_, Scalar>",signature)


if __name__=='__main__':unittest.main()
