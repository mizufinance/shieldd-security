"""Paged protocol tests; synthetic bytes never qualify an actual capture."""
import copy,json,unittest
from pathlib import Path
from blake3 import blake3
from circuits import transfer_note_hash_pages as pages,transfer_relation as relation
from integration import note_hash_observer as hooks,note_spend_observer as spends
from tests.test_transfer_note_hash import boundary_fixture
from tests.test_transfer_note_spend import encoded


class NoteHashPageTests(unittest.TestCase):
    def fixture(self):
        obj,note,caller=boundary_fixture('nullifier',0,0)
        obj.update(ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False)
        data=encoded(obj);digest=blake3(data).hexdigest()
        manifest=dict(schema='shieldd-transfer-note-hash-pages-v1',family='transfer',scope=pages.SCOPE,
            **{key:obj[key] for key in ('relation_digest','domain_size','full_rows','constant_copy')},
            ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,
            pages=[dict(ordinal=i,slot=slot,role=role,level=level,block=block,blake3=digest)
                   for i,(slot,role,level,block) in enumerate(pages.inventory())])
        return manifest,data,note,caller

    def test_already_qualified_manifest_only_and_pending_page_view(self):
        manifest,data,note,caller=self.fixture()
        view=pages.qualified_page(encoded(manifest),data,2,note,caller)
        self.assertTrue(json.loads(view)['ordinary_full_ordered_rows_equal'])
        self.assertFalse(json.loads(data)['ordinary_full_ordered_rows_equal'])
        self.assertEqual(len(pages.inventory()),55)
        self.assertEqual(pages.inventory()[-1],(1,'dummy',0,0))

    def test_truncation_duplicate_order_pending_and_page_identity_refusals(self):
        manifest,data,note,caller=self.fixture()
        for mutation in (lambda m:m['pages'].pop(),lambda m:m['pages'].append(m['pages'][-1]),
                         lambda m:m['pages'].__setitem__(3,m['pages'][2]),
                         lambda m:m.update(repeated_observations_equal=False)):
            changed=copy.deepcopy(manifest);mutation(changed)
            with self.assertRaises(relation.RelationError):pages.qualified_page(encoded(changed),data,2,note,caller)
        with self.assertRaisesRegex(relation.RelationError,'bytes/digest'):pages.qualified_page(encoded(manifest),data+b' ',2,note,caller)
        with self.assertRaisesRegex(relation.RelationError,'role or identity'):pages.qualified_page(encoded(manifest),data,3,note,caller)

    def test_existing_four_compile_fullrow_qualifier_is_preserved(self):
        base=Path('tests/fixtures/current-transfer-ownership-inspection.rs').read_bytes()
        one=spends.instrument_exporter(base,Path('integration/observers/note_spend_export.rs').read_bytes())
        one=hooks.instrument_exporter(one,Path('integration/observers/note_hash_export.rs').read_bytes())
        result=hooks.instrument_pages_exporter(one,Path('integration/observers/note_hash_pages_export.rs').read_bytes())
        self.assertEqual(result.count(b'compare_framed_rows(&paths[0], path, 200770, 262144)?;'),1)
        self.assertIn(b'qualify_note_hash_pages(first,repeated,&pending)?;',result)
        self.assertIn(b'pending == repeat',result)
        with self.assertRaises(ValueError):hooks.instrument_pages_exporter(result,b'')


if __name__=='__main__':unittest.main()
