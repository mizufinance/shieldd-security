"""Exact24state boundary joins and refusal to compose metadata-only hashes."""
import copy,io,tempfile,unittest
from pathlib import Path
from circuits import generate_note_tree_path as path,transfer_note_tree as tree,transfer_relation as relation
from tests.test_note_tree import tree_fixture,state_page
from tests.test_transfer_note_spend import encoded


class NoteTreePathTests(unittest.TestCase):
    def fixture(self):
        obj,note,caller,stream,_=tree_fixture()
        pages=[]
        for i in range(24):
            page=state_page(obj,i);page.update(ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)
            pages.append(encoded(page))
        return encoded(obj),pages,note,caller,stream

    def test_all24_native_level_source_boundaries_required_in_order(self):
        data,pages,note,caller,_=self.fixture()
        self.assertEqual(len(path.inspect_pages(data,pages,note,caller,0)['levels']),48)
        for changed in (pages[:-1],pages+[pages[-1]],list(reversed(pages))):
            with self.assertRaises(relation.RelationError):path.inspect_pages(data,changed,note,caller,0)
        with self.assertRaises(relation.RelationError):path.inspect_pages(data,pages,note,caller,1)
        changed=copy.deepcopy(pages);page=relation.record(changed[7]);page['hash']['output']=page['hash']['inputs'][1]
        page['hash']['blocks'][0]['after'][1]=page['hash']['output'];changed[7]=encoded(page)
        with self.assertRaisesRegex(relation.RelationError,'exact source order'):path.inspect_pages(data,changed,note,caller,0)

    def test_metadata_only_permutations_never_become_path_proofs(self):
        data,pages,note,caller,stream=self.fixture()
        selected=[tree.extract_level(data,io.BytesIO(stream.getvalue()),note,caller,0,i) for i in range(24)]
        with tempfile.TemporaryDirectory() as directory:
            generated=path.generate(data,selected,pages,[{}]*24,note,caller,Path(directory),0)
            # The first exact tree15row theorem can be emitted; the next batch
            # must refuse this boundary-only fixture's missing all-lane DAG.
            module,source=next(generated)
            self.assertEqual(module,'RuntimeTransferNoteTree0Level0')
            self.assertIn('theorem ordered_children',source)
            with self.assertRaisesRegex(relation.RelationError,'missing source node'):next(generated)


if __name__=='__main__':unittest.main()
