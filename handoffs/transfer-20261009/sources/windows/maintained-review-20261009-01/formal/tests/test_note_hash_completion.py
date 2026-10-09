"""Actual captured round construction/preservation and ownership refusal tests."""
import tempfile,unittest
from pathlib import Path
from circuits import transfer_note_hash as hashes,generate_note_hash_completion as completion,transfer_relation as relation
from tests.test_transfer_note_hash import hash_fixture
from tests.test_transfer_note_spend import encoded


class NoteHashCompletionTests(unittest.TestCase):
    def setUp(self):
        obj,self.note,self.caller,artifact,stream=hash_fixture();self.data=encoded(obj)
        self.directory=tempfile.TemporaryDirectory();self.root=Path(self.directory.name)
        (self.root/'poseidon381-wide.json').write_bytes(encoded(artifact))
        self.extracted=hashes.extract(self.data,stream,self.note,self.caller,self.root)
    def tearDown(self):self.directory.cleanup()

    def test_actual_full_partial_terminal_round_steps_and_source_proof_contract(self):
        for index in (0,4,61,64):
            plan=completion.completion_plan(self.data,self.extracted,self.note,self.caller,self.root,index)
            self.assertEqual(len(plan['steps'])%3,0)
            self.assertEqual([s['kind'] for s in plan['steps']],['square','square','product']*(len(plan['steps'])//3))
            self.assertEqual(len(plan['writes']),4*(len(plan['steps'])//3))
            self.assertFalse(set(plan['writes'])&set(plan['kept']))
            self.assertTrue({0,1,2,1000}<=set(plan['kept']))
            self.assertEqual(set(plan['coverage']),set(plan['raw']))
            modules=completion.generate(self.data,self.extracted,self.note,self.caller,self.root,index)
            text=modules[1][1]
            self.assertEqual(text.count('#print axioms'),9)
            self.assertIn('CompilerCompletion.Topological kept [] completionSteps',text)
            self.assertIn('CompilerCompletion.original_rows_complete',text)
            self.assertIn('PoseidonCompletion.run_outside',text)
            self.assertIn('CompilerOrder.checked_order',text)
            self.assertIn('set_option maxRecDepth 4096',text)
            self.assertNotIn('Topological kept [] completionSteps := by decide',text)
            self.assertIn('or_false,or_assoc]',text)
            signature=text[text.index('theorem complete_round'):text.index(' := by',text.index('theorem complete_round'))]
            self.assertNotIn('(satisfied :',signature)
            self.assertNotIn('(state',signature)

    def test_constructed_numeric_round_rows_for_arbitrary_initial_assignment(self):
        plan=completion.completion_plan(self.data,self.extracted,self.note,self.caller,self.root,4)
        p=relation.MODULUS;rho={c:(7*c+3)%p for c in range(2048)};rho[0]=rho[1000]=1
        before=dict(rho);evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
        for step in plan['steps']:
            left=evaluate(step['left']);rem=evaluate(step['remainder'])
            value=left**2 if step['kind']=='square' else left*evaluate(step['right'])
            if step['kind']=='product':rho[step['auxiliary']]=(left-evaluate(step['right']))**2%p
            rho[step['output']]=(value-rem)%p
        self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['raw'].values()))
        self.assertTrue(all(rho[c]==before[c] for c in range(2048) if c not in plan['writes']))
        rho[plan['writes'][0]]=(rho[plan['writes'][0]]+1)%p
        self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['raw'].values()))

    def test_nonunit_ambiguous_and_shared_pivots_are_refused(self):
        for output,occupied in ((((10,2),),set()),(((10,1),(11,1)),set()),(((10,1),),{10})):
            with self.assertRaises(relation.RelationError):completion._pivot(output,occupied)
        with self.assertRaises(relation.RelationError):completion.completion_plan(self.data,self.extracted,self.note,self.caller,self.root,True)


if __name__=='__main__':unittest.main()
