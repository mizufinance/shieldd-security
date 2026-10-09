"""Folded ownership plans only; actual six-loop constructors/kernel are OPEN."""
import copy,unittest
from circuits import transfer_epk_fixed_batch as batch,transfer_epk_fixed_composition as composition,transfer_relation as relation
from tests.test_transfer_epk_fixed_batch import selected_fixture
from tests.test_transfer_epk_fixed import encoded

class EpkCompositionTests(unittest.TestCase):
    def test_complete126_programs_and_public_shared_roles(self):
        checked,combined,prefixes,(parent,raw,capsules,caller)=selected_fixture();extracted=batch._partition(checked,combined,prefixes)
        plan=composition.plan(encoded(parent),raw,capsules,caller,extracted)
        self.assertEqual(len(plan['loops']),6);self.assertEqual(plan['writes'],[])
        self.assertEqual(plan['rows'],list(range(1513)))
        for loop in plan['loops']:
            self.assertEqual([p['index'] for p in loop['programs']],list(range(126)))
            self.assertTrue({0,1,2,200692}<=set(loop['kept']))
            self.assertEqual(len(loop['bit_sources']),252)
            self.assertEqual(loop['scalar_source'],parent['scopes'][loop['scope_id']]['randomizer'])
        self.assertIn('every column outside',plan['universal_frame'])
        self.assertIn('canonical/native/local kernel/frame instantiation OPEN',plan['scope'])

    def test_replay_source_and_original_row_ownership_not_trusted(self):
        for edit in ('hash','rows','capsule','order'):
            checked,combined,prefixes,(parent,raw,capsules,caller)=selected_fixture();extracted=batch._partition(checked,combined,prefixes)
            if edit=='hash':extracted['parent_sha256']='f'*64
            elif edit=='rows':extracted['pages'][0]['rows'].pop()
            elif edit=='capsule':capsules['metadata']['capsules'][0]['epk_inverse']={'source':[1,999]}
            else:parent['scopes'].reverse()
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):composition.plan(encoded(parent),raw,capsules,caller,extracted)
