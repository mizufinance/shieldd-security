"""Exact NOTE15/8 absorption/source/row construction controls."""
import copy,io,tempfile,unittest
from pathlib import Path
from circuits import generate_note_hash_call_completion as calls,transfer_note_hash as hashes
from circuits import transfer_note_hash_join as joins,generate_note_hash_block_completion as blocks
from circuits import transfer_relation as relation
from tests.note_hash_call_fixture import fixture_two_blocks
from tests.test_transfer_note_spend import encoded
from tests.test_note_hash_block_completion import native_rounds


class NoteHashCallCompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pages,cls.note,cls.caller,cls.artifact,stream=fixture_two_blocks()
        cls.directory=tempfile.TemporaryDirectory();cls.root=Path(cls.directory.name)
        (cls.root/'poseidon381-wide.json').write_bytes(encoded(cls.artifact))
        cls.extractions=[hashes.extract(data,io.BytesIO(stream.getvalue()),cls.note,cls.caller,cls.root) for data in cls.pages]
    @classmethod
    def tearDownClass(cls):cls.directory.cleanup()

    def test_second_block_first_round_reads_captured_absorbed_boundary(self):
        checked=joins.inspect_calls(self.pages,self.note,self.caller)
        self.assertEqual([x['metadata']['block'] for x in checked],[0,1])
        plan=blocks.chunk_plan(self.pages[1],self.extractions[1],self.note,self.caller,self.root,0,1)
        p=relation.MODULUS;rho={c:(41*c+5)%p for c in range(4096)};rho[0]=rho[4000]=1
        initial=dict(rho);evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
        state=[evaluate(lc) for lc in plan['selected']['calls'][0]['segments'][0]['before']]
        for step in plan['steps']:
            left=evaluate(step['left']);remainder=evaluate(step['remainder'])
            if step['kind']=='square':value=left*left
            else:
                right=evaluate(step['right']);value=left*right;rho[step['auxiliary']]=(left-right)**2%p
            rho[step['output']]=(value-remainder)%p
        self.assertEqual([evaluate(lc) for lc in plan['selected']['calls'][0]['segments'][0]['after']],
                         native_rounds(state,self.artifact,0,1))
        self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['raw'].values()))
        self.assertTrue(all(rho[c]==initial[c] for c in initial if c not in plan['writes']))
        source=calls._composition('RuntimeNoteHash0Commitment0',checked[0]['metadata'])
        self.assertEqual(source.count('#print axioms'),8)
        signature=source[source.index('theorem complete_hash'):source.index(' := by',source.index('theorem complete_hash'))]
        self.assertNotIn('(satisfied :',signature)
        self.assertNotIn('absorbedState',signature)
        self.assertIn('prior_preserved',source)
        self.assertIn('actual_hash_sound',source)
        leaf=joins.generate(self.pages,self.extractions,self.note,self.caller,self.root)[-1][1]
        self.assertIn('  dsimp only at coordinate\n',leaf)
        self.assertLess(leaf.index('dsimp only at coordinate'),leaf.index('rw [← output_equal] at coordinate'))

    def test_missing_reordered_pages_and_semantic_absorption_changes_refused(self):
        for changed in (self.pages[:1],list(reversed(self.pages))):
            with self.assertRaisesRegex(relation.RelationError,'missing/reordered'):
                next(calls.generate(changed,self.extractions,self.note,self.caller,self.root))
        changed=relation.record(self.pages[1]);changed['hash']['blocks'][1]['before'][1]=changed['hash']['inputs'][5]
        with self.assertRaisesRegex(relation.RelationError,'absorbed state LC mismatch'):
            next(calls.generate([self.pages[0],encoded(changed)],self.extractions,self.note,self.caller,self.root))
        changed=copy.deepcopy(self.extractions);changed[1]['selected_rows'].pop()
        with self.assertRaisesRegex(relation.RelationError,'missing'):
            next(calls.generate(self.pages,changed,self.note,self.caller,self.root))


if __name__=='__main__':unittest.main()
