"""Tiny source-composition controls. These fixtures are not Rust or captures."""
import unittest

from integration import transfer_remaining_observer as observer


def fixture():
    files = {}
    for path, operations in observer.hooks().items():
        text = '// synthetic source anchor fixture, never runtime evidence\n'
        # Some later anchors are introduced by earlier hooks.
        for operation in operations:
            anchor = operation['anchor']
            if not any(anchor in earlier['replacement'] for earlier in
                       operations[:operations.index(operation)]):
                text += anchor + '\n'
        files[path] = text.encode()
    files[observer.CATALOGUE] = b'// retained parent catalogue\n'
    files[observer.EXPORTER] = (observer.DISPATCH +
        '\n// retained asset v2, RK, recovery74 and old modes\n' +
        observer.QUALIFIER_SCHEMA + '\n' + observer.QUALIFIER_BRANCH + '\n').encode()
    files['untouched'] = b'parent bytes\r\n'
    return files


class RemainingObserverTests(unittest.TestCase):
    def test_complete_append_preserves_unrelated_and_old_exporter(self):
        source = fixture()
        result = observer.compose(source)
        self.assertEqual(result['untouched'], source['untouched'])
        self.assertEqual(set(result), set(source) | {observer.MODULE})
        self.assertEqual(result[observer.EXPORTER].count(observer.MODE.encode()), 1)
        old = result[observer.EXPORTER].split(b'// Called only after')[0]
        old = old.replace(observer.MODE.encode(), b'').replace(observer.QUALIFIER_ADD.encode(), b'')
        old = old.replace(b'        Some("shieldd-transfer-remaining-source-pages-v1") |\n', b'')
        self.assertEqual(old.rstrip(),
                         source[observer.EXPORTER].rstrip())
        self.assertNotIn(observer.MODULE, source)

    def test_wrong_live_comparator_body_refused(self):
        source = fixture()
        path = observer.PREFIX + 'src/volume.rs'
        source[path] = source[path].replace(b'less_or_equal_bounded', b'changed_comparator')
        with self.assertRaisesRegex(ValueError, 'anchor drift'):
            observer.compose(source)

    def test_duplicate_live_caller_anchor_refused(self):
        source = fixture()
        path = observer.PREFIX + 'src/transfer.rs'
        source[path] += b'    let external = !same_address;\n'
        with self.assertRaisesRegex(ValueError, 'anchor drift'):
            observer.compose(source)

    def test_incomplete_parent_and_existing_child_refused(self):
        source = fixture()
        del source[observer.EXPORTER]
        with self.assertRaisesRegex(ValueError, 'retained'):
            observer.compose(source)
        source = fixture()
        source[observer.MODULE] = b'existing'
        with self.assertRaisesRegex(ValueError, 'fresh'):
            observer.compose(source)

    def test_operation_boolean_count_is_not_one(self):
        operation = {'anchor': 'original', 'replacement': 'hooked original',
                     'kind': 'replace', 'expected_count': True}
        with self.assertRaisesRegex(ValueError, 'invalid'):
            observer.instrument(b'original\n', [operation])

    def test_line_endings_preserved_and_mixed_refused(self):
        operation = {'anchor': 'original', 'replacement': 'hooked\noriginal',
                     'kind': 'replace', 'expected_count': 1}
        self.assertEqual(observer.instrument(b'original\r\n', [operation]),
                         b'hooked\r\noriginal\r\n')
        with self.assertRaisesRegex(ValueError, 'mixed'):
            observer.instrument(b'original\r\nother\n', [operation])

    def test_raw_nk_and_two_distinct_amount_slots_retained(self):
        operations = observer.hooks()[observer.PREFIX + 'src/transfer.rs']
        text = '\n'.join(o['replacement'] for o in operations)
        self.assertIn('&auth.nk, &auth.effective_nk', text)
        self.assertIn('&outputs[0].note.amount, &outputs[1].note.amount', text)
        roles = (observer.FRAGMENTS / 'transfer_remaining_roles.rs').read_text()
        self.assertIn('volume[10]==auth[0]', roles)
        self.assertIn('encryption[3]==notes[6]', roles)
        self.assertIn('routing[1]==notes[7]', roles)
        self.assertIn('ordered.len()==64 && ordered==fields', roles)

    def test_pending_page_hash_uses_actual_written_newline(self):
        text = (observer.FRAGMENTS / 'transfer_remaining_export.rs').read_text()
        self.assertIn("bytes.push(b'\\n')", text)
        self.assertIn('"qualification":false', text)


if __name__ == '__main__':
    unittest.main()
