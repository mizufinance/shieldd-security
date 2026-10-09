"""Complete-call boundaries and actual one-block generator controls."""
import copy,json,tempfile,unittest
from pathlib import Path
from circuits import transfer_note_hash_join as joins,transfer_note_hash as hashes,transfer_relation as relation
from tests.test_transfer_note_hash import hash_fixture,boundary_fixture
from tests.test_transfer_note_spend import encoded


class NoteHashJoinTests(unittest.TestCase):
    def test_actual_one_block_rounds_are_shared_and_full_native_inputs_retained(self):
        obj,note,caller,artifact,stream=hash_fixture();data=encoded(obj)
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'poseidon381-wide.json').write_bytes(encoded(artifact))
            extracted=hashes.extract(data,stream,note,caller,root)
            modules=joins.generate([data],[extracted],note,caller,root)
        self.assertEqual(len(modules),16)
        joined=modules[-1][1]
        self.assertEqual(joined.count('#print axioms'),3)
        self.assertEqual(joined.count('set_option pp.all true in'),3)
        self.assertIn('Poseidon.initialLinear 1 5',joined)
        self.assertIn('theorem actual_hash_sound',joined)
        self.assertIn('permutation_sound rho one satisfied',joined)
        self.assertNotIn('(block :',joined)
        self.assertNotIn('sorry',joined)
        self.assertEqual(sum(source.count('theorem certificate_') for _,source in modules),65)
        changed=copy.deepcopy(extracted);changed['selected_rows'].pop()
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'poseidon381-wide.json').write_bytes(encoded(artifact))
            with self.assertRaises(relation.RelationError):joins.generate([data],[changed],note,caller,root)

    def test_two_commitment_blocks_must_have_identical_calls_and_order(self):
        first,note,caller=boundary_fixture('commitment',0,0)
        second=copy.deepcopy(first);second['block']=1
        joins.inspect_calls([encoded(first),encoded(second)],note,caller)
        for pages in ([encoded(first)],[encoded(second),encoded(first)],
                      [encoded(first),encoded(first)]):
            with self.assertRaises(relation.RelationError):joins.inspect_calls(pages,note,caller)
        changed=copy.deepcopy(second);changed['hash']['blocks'][0]['after'][0]=changed['hash']['blocks'][0]['after'][1]
        with self.assertRaises(relation.RelationError):joins.inspect_calls([encoded(first),encoded(changed)],note,caller)
        changed=copy.deepcopy(second);changed['expressions'][0]['terms'][0][1]=f'{2:064x}'
        with self.assertRaises(relation.RelationError):joins.inspect_calls([encoded(first),encoded(changed)],note,caller)


if __name__=='__main__':unittest.main()
