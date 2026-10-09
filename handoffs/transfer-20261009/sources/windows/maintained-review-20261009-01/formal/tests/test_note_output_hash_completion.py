"""Construct both exact output hashes without supplied-equality premises."""
import copy,io,tempfile,unittest
from pathlib import Path
from circuits import generate_note_output_hash_completion as completion,generate_note_hash_block_completion as blocks
from circuits import transfer_note_output_hash as hashes,transfer_relation as relation
from tests.test_note_output_hash import fixture
from tests.test_transfer_note_spend import encoded
from tests.test_note_hash_block_completion import native_rounds


class OutputHashCompletionTests(unittest.TestCase):
    def test_both_native_calls_construct_all_rows_and_preserve_every_outside_column(self):
        for role in ('note','recovery'):
            pages,outputs,caller,artifact,rows=fixture(role)
            with tempfile.TemporaryDirectory() as directory:
                root=Path(directory);(root/'poseidon381-wide.json').write_bytes(encoded(artifact))
                extracted=[hashes.extract(page,io.BytesIO(rows),outputs,caller,root) for page in pages]
                p=relation.MODULUS;rho={c:(37*c+9)%p for c in range(4096)};rho[0]=rho[4000]=1
                original=dict(rho);owned=set();actual={};initial_inputs=None
                evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
                for block,(page,selected) in enumerate(zip(pages,extracted)):
                    context=completion._context(page,selected,outputs,caller,root)
                    call=context[1]['metadata']['hash']
                    if initial_inputs is None:initial_inputs=[evaluate(context[1]['observed'][tuple(ref['source'])]) for ref in call['inputs']]
                    state=([256*len(initial_inputs)+call['domain'],0,0,0,0,0] if block==0 else state)
                    for lane,value in enumerate(initial_inputs[5*block:5*(block+1)],1):state[lane]=(state[lane]+value)%p
                    for start in range(0,65,5):
                        plan=blocks._chunk_plan(context,start,min(start+5,65));before=list(state)
                        for step in plan['steps']:
                            left=evaluate(step['left']);remainder=evaluate(step['remainder'])
                            if step['kind']=='square':value=left*left
                            else:
                                right=evaluate(step['right']);value=left*right;rho[step['auxiliary']]=(left-right)**2%p
                            rho[step['output']]=(value-remainder)%p
                        state=native_rounds(before,artifact,start,min(start+5,65))
                        self.assertEqual([evaluate(lc) for lc in plan['selected']['calls'][0]['segments'][min(start+4,64)]['after']],state)
                        owned.update(plan['writes']);actual.update(plan['raw'])
                self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in actual.values()))
                self.assertTrue(all(rho[c]==original[c] for c in original if c not in owned))
                self.assertEqual(evaluate(context[1]['observed'][tuple(call['output']['source'])]),state[1])
                supplied=context[1]['metadata']['supplied_commitment']
                # Local hash construction must not silently manufacture the
                # separate binding to a caller-supplied commitment witness.
                self.assertNotEqual(state[1],evaluate(context[1]['observed'][tuple(supplied['source'])]))
                modules=list(completion.generate(pages,extracted,outputs,caller,root))
                self.assertEqual(len(modules),60)
                final=modules[-1][1];signature=final[final.index('theorem complete_hash'):final.index(' := by',final.index('theorem complete_hash'))]
                self.assertNotIn('(satisfied :',signature);self.assertNotIn('supplied_commitment',signature)
                self.assertIn(f'        {call["domain"]} (',signature)
                self.assertEqual(final.count('#print axioms'),8)
                rho[max(owned)]=(rho[max(owned)]+1)%p
                self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in actual.values()))

    def test_reordered_blocks_missing_rows_and_changed_native_constructor_refuse(self):
        pages,outputs,caller,artifact,rows=fixture('recovery')
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'poseidon381-wide.json').write_bytes(encoded(artifact))
            extracted=[hashes.extract(page,io.BytesIO(rows),outputs,caller,root) for page in pages]
            with self.assertRaises(relation.RelationError):next(completion.generate(pages[::-1],extracted,outputs,caller,root))
            changed=copy.deepcopy(extracted);changed[1]['selected_rows'].pop()
            with self.assertRaises(relation.RelationError):next(completion.generate(pages,changed,outputs,caller,root))


if __name__=='__main__':unittest.main()
