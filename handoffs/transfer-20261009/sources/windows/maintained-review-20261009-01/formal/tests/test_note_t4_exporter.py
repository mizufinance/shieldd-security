"""Maintained exporter promotion reproduces reviewed recipe and old paths."""
import hashlib,unittest
from pathlib import Path
from integration import note_spend_observer as spends,note_hash_observer as hashes,note_tree_observer as trees


def compose():
    root=Path(__file__).resolve().parents[1]
    data=(root/'tests/fixtures/current-transfer-ownership-inspection.rs').read_bytes()
    for recipe,resource in ((spends.instrument_exporter,'note_spend_export.rs'),
        (hashes.instrument_exporter,'note_hash_export.rs'),
        (hashes.instrument_pages_exporter,'note_hash_pages_export.rs'),
        (trees.instrument_exporter,'note_t4_pages_export.rs')):
        data=recipe(data,(root/'integration/observers'/resource).read_bytes())
    return data


class MaintainedNoteT4ExporterTests(unittest.TestCase):
    def test_exact_reviewed_composition_and_preserved_native_capture_bodies(self):
        old=Path('tests/fixtures/current-transfer-ownership-inspection.rs').read_bytes()
        current=Path('integration/src/bin/transfer-ownership-inspection.rs').read_bytes()
        self.assertEqual(current,compose())
        self.assertEqual(hashlib.sha256(current).hexdigest(),'e483f869f1775372faf5384f8ebd845a65e64af853fed711c8cd96b82a78c228')
        # Everything after original main's dispatch remains exact, including
        # fixed/roles/hash capture bodies and original native unit test module.
        marker=b'fn capture_fixed_spend('
        self.assertTrue(current[current.index(marker):].startswith(old[old.index(marker):]))
        prefix=b'fn qualified_metadata('
        self.assertEqual(current[:current.index(prefix)],old[:old.index(prefix)])
        for mode in ('roles-spool','ordinary-spool','fixed-spend-spool','note-spend-spool',
                     'note-hash-spool','note-hash-pages-spool','note-t4-pages-spool','qualify-spools'):
            self.assertIn(mode.encode(),current)

    def test_complete_ordered_fourspool_qualification_precedes_new_page_checks(self):
        current=compose()
        full=current.index(b'compare_framed_rows(&paths[0], path, 200770, 262144)?;')
        repeated=current.index(b'pending == repeat')
        pages=current.index(b'qualify_note_t4_pages(first,repeated,&pending)?;')
        flags=current.index(b'pending["ordinary_full_ordered_rows_equal"] = json!(true);')
        self.assertLess(full,repeated);self.assertLess(repeated,pages);self.assertLess(pages,flags)
        self.assertEqual(current.count(b'fn capture_note_t4_pages('),1)
        self.assertIn(b'count == 56 && copy == 200692',current)
        self.assertIn(b'bytes == repeat && descriptor["blake3"]',current)


if __name__=='__main__':unittest.main()
