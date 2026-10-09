"""Construct actual multi-round rows and compare an independent field recurrence."""
import copy,tempfile,unittest
from pathlib import Path
from circuits import generate_note_hash_block_completion as block,transfer_note_hash as hashes
from circuits import transfer_relation as relation
from tests.test_transfer_note_hash import hash_fixture
from tests.test_transfer_note_spend import encoded


def native_rounds(state,artifact,start,stop):
    p=relation.MODULUS;ark=[[int(v,16) for v in row] for row in artifact['ark']]
    mds=[[int(v,16) for v in row] for row in artifact['mds']]
    for r in range(start,stop):
        state=[(v+a)%p for v,a in zip(state,ark[r])]
        for lane in (range(6) if r<4 or r>=61 else range(1)):state[lane]=pow(state[lane],5,p)
        state=[sum(a*v for a,v in zip(row,state))%p for row in mds]
    return state


class NoteHashBlockCompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        obj,cls.note,cls.caller,cls.artifact,stream=hash_fixture();cls.data=encoded(obj)
        cls.directory=tempfile.TemporaryDirectory();cls.root=Path(cls.directory.name)
        (cls.root/'poseidon381-wide.json').write_bytes(encoded(cls.artifact))
        cls.extracted=hashes.extract(cls.data,stream,cls.note,cls.caller,cls.root)
    @classmethod
    def tearDownClass(cls):cls.directory.cleanup()

    def test_five_actual_rounds_construct_preserve_and_match_native_recurrence(self):
        plan=block.chunk_plan(self.data,self.extracted,self.note,self.caller,self.root,0,5)
        p=relation.MODULUS;rho={c:(13*c+17)%p for c in range(2048)};rho[0]=rho[1000]=1
        before=dict(rho);evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
        initial=[evaluate(lc) for lc in plan['selected']['calls'][0]['segments'][0]['before']]
        for step in plan['steps']:
            left=evaluate(step['left']);remainder=evaluate(step['remainder'])
            if step['kind']=='square':value=left*left
            else:
                right=evaluate(step['right']);value=left*right
                rho[step['auxiliary']]=(left-right)**2%p
            rho[step['output']]=(value-remainder)%p
        self.assertEqual([evaluate(lc) for lc in plan['selected']['calls'][0]['segments'][4]['after']],
                         native_rounds(initial,self.artifact,0,5))
        self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['raw'].values()))
        self.assertTrue(all(rho[c]==before[c] for c in before if c not in plan['writes']))
        name,source=block._chunk_source('RuntimeNoteHash0State0',0,plan,[])
        self.assertEqual(source.count('#print axioms'),10)
        self.assertIn('CompilerOrder.checked_order',source)
        self.assertIn('prior_support_checked',source)
        self.assertNotIn('Topological kept [] completionSteps := by decide',source)
        rho[plan['writes'][-2]]=(rho[plan['writes'][-2]]+1)%p
        self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['raw'].values()))
        chunks=['RuntimeNoteHash0State0CompletionChunk'+str(i) for i in range(13)]
        joined=block._composition('RuntimeNoteHash0State0',chunks,relation.record(self.data))
        self.assertEqual(joined.count('#print axioms'),6)
        signature=joined[joined.index('theorem complete_hash'):joined.index(' := by',joined.index('theorem complete_hash'))]
        self.assertNotIn('(satisfied :',signature)
        self.assertIn('sound_coverage_checked',joined)
        self.assertIn('prior_preserved',joined)

    def test_invalid_chunk_and_missing_actual_row_refused(self):
        for bounds in ((True,5),(5,5),(0,6),(64,66)):
            with self.assertRaises(relation.RelationError):
                block.chunk_plan(self.data,self.extracted,self.note,self.caller,self.root,*bounds)
        changed=copy.deepcopy(self.extracted);changed['selected_rows'].pop()
        with self.assertRaisesRegex(relation.RelationError,'missing'):
            block.chunk_plan(self.data,changed,self.note,self.caller,self.root,0,1)

    def test_last_chunk_uses_linear_fence_and_bounded_ordered_coverage(self):
        context=block._context(self.data,self.extracted,self.note,self.caller,self.root)
        chunks=['RuntimeNoteHash0State0CompletionChunk'+str(i) for i in range(13)]
        plan=block._chunk_plan(context,60,65)
        _,source=block._chunk_source('RuntimeNoteHash0State0',12,plan,chunks[:12])
        proof=source[source.index('theorem prior_support_checked'):source.index('theorem prior_preserved')]
        self.assertIn('ColumnFence.checked_rows',proof)
        self.assertIn('ColumnFence.checkRows',proof)
        self.assertNotIn('ownedWrites))) = true := by decide',proof)
        order=source[source.index('theorem ordered :'):source.index('theorem writes_exact')]
        self.assertEqual(order.count('CompilerOrder.checkOrder kept [] partSteps'),5)
        self.assertEqual(order.count('CompilerOrderComposition.append'),4)
        self.assertIn('CompilerOrderComposition.check_order',order)
        self.assertNotIn('checkOrder kept [] completionSteps = true := by decide',order)
        joined=block._composition('RuntimeNoteHash0State0',chunks,relation.record(self.data))
        coverage=joined[joined.index('theorem sound_coverage_checked'):joined.index('theorem preserves')]
        self.assertEqual(coverage.count('List.Sublist ('),65)
        self.assertEqual(coverage.count('localRows.subset member'),65)
        self.assertEqual(coverage.count('have chunkIncluded'),13)
        self.assertNotIn('= true := by decide',coverage)
        # Independently validate ordered source row inclusion into the five-round
        # chunks. Constant-link repetition prevents equality of whole row lists.
        for start in range(0,65,5):
            chunk=block._chunk_plan(context,start,min(start+5,65))
            indices=list(chunk['raw'])
            for segment in context[0]['calls'][0]['segments'][start:start+5]:
                expected=sorted(set(segment['rows'])|{context[0]['constant_link']})
                positions=[indices.index(i) for i in expected]
                self.assertEqual(positions,sorted(positions))
                self.assertEqual([chunk['raw'][i] for i in expected],
                    [context[0]['rows'][i] for i in expected])


if __name__=='__main__':unittest.main()
