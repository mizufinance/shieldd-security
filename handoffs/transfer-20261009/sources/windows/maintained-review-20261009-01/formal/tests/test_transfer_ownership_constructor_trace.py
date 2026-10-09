"""Finite source-only fixtures for the actual whole constructor renderer."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_constructor_trace as generator
from circuits.transfer_relation import RelationError


def fixture():
    chunks = [dict(metadata=dict(schema='shieldd-transfer-ownership-v1',window_start=start,
        window_count=min(16,126-start),constant_copy=200692)) for start in range(0,126,16)]
    selections = [{} for _ in chunks]
    def plan(checked, extracted, offset, *args):
        index = checked['metadata']['window_start']+offset
        return dict(writes=[2257+2*index,2258+2*index,51233+2*index,51234+2*index])
    return chunks,selections,plan


class ConstructorTraceTests(unittest.TestCase):
    def render(self, values):
        chunks,selections,plan = values
        with patch.object(generator.candidates,'validate_all_chunks',return_value={}) as accepted, \
             patch.object(generator.completion,'window_plan',side_effect=plan), \
             patch.object(generator.joins,'actual_window_partition',return_value={}) as partitions:
            result = generator.generate(chunks,selections)
            accepted.assert_called_once_with(chunks,selections)
            self.assertEqual(partitions.call_count,126)
            return result

    def test_opaque_eight_chunks_reuse_symbolic_rules(self):
        name,source = self.render(fixture())
        self.assertEqual(name,'RuntimeOwnershipConstructorTrace')
        self.assertEqual(source.count('#check @'),10)
        self.assertEqual(source.count('#print axioms'),10)
        self.assertEqual(source.count('import ShielddSecurity.RuntimeOwnershipConstructorChunk'),8)
        self.assertIn('GroupCircuitProgramTrace.aligned_append',source)
        self.assertIn('bounded_fresh',source)
        self.assertIn('unfold segments beforeFrame',source)
        self.assertIn('unfold programs input',source)
        self.assertEqual((name,source),generator._render(200692))
        self.assertEqual(source.count('private theorem boundary'),7)
        for index in range(7):
            self.assertIn(f'RuntimeOwnershipConstructorChunk{16*index:03d}.afterFrame = RuntimeOwnershipConstructorChunk{16*(index+1):03d}.beforeFrame',source)
            self.assertIn(f'rw [frame{index},boundary{index}]',source)
        self.assertIn('GroupVariableCircuitCompletion.constructs',source)
        self.assertIn('(precomputed : Satisfies base priorRows)',source)
        self.assertIn('RuntimeOwnershipConstructorChunk112.protected_programs',source)
        self.assertIn('RuntimeOwnershipConstructorChunk000.programs bits ++ (RuntimeOwnershipConstructorChunk016.programs bits ++ (RuntimeOwnershipConstructorChunk032.programs bits',source)
        self.assertNotIn('namespace C0 :=',source)
        self.assertNotIn('theorem protected ',source)
        self.assertNotIn('native_decide',source)
        # This scoped stitching theorem does not claim native scalar semantics.
        self.assertNotIn('nsmul',source)
        self.assertNotIn('Desired',source)

    def test_shape_order_family_and_actual_write_gaps_refuse(self):
        for change in ('few','reordered','count','family','gap','randomizer','low','copy'):
            chunks,selections,plan = fixture()
            if change=='few': chunks.pop(); selections.pop()
            elif change=='reordered': chunks[1]['metadata']['window_start']=32
            elif change=='count': chunks[-1]['metadata']['window_count']=13
            elif change=='family': chunks[2]['metadata']['schema']='shieldd-transfer-rnk-dh-v1'
            else:
                original=plan
                def plan(checked,extracted,offset,*args):
                    result=copy.deepcopy(original(checked,extracted,offset,*args))
                    if checked['metadata']['window_start']==16 and offset==0:
                        if change=='gap':result['writes'][0]+=1
                        elif change=='randomizer':result['writes'].append(3766)
                        elif change=='low':result['writes'][0]=1980
                        else:result['writes'].append(200692)
                    return result
            with self.subTest(change=change),self.assertRaises(RelationError):
                self.render((chunks,selections,plan))


if __name__=='__main__':unittest.main()
