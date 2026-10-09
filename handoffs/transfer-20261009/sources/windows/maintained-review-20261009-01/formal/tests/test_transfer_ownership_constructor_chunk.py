"""Bounded finite adapter fixtures; all actual/kernel qualification separate."""
import copy,unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_constructor_chunk as generator
from circuits.transfer_relation import RelationError


def fixture(count=1):
    point=lambda x,y:(('source',(1,x)),('source',(1,y)))
    checked=dict(metadata=dict(schema='shieldd-transfer-ownership-v1',window_start=0,
        window_count=count,relation_digest='a'*64,domain_size=262144,full_rows=200770,
        constant_copy=200692),bits=[(1,column) for column in range(2000,2252)],
        points=dict(base=point(1504,1505),twice=point(2253,2254),triple=point(2255,2256)),
        derived={(1,column):((column,1),) for column in range(1500,2300)},windows=[])
    previous=point(1,2);plans=[]
    for offset in range(count):
        output=point(2257+2*offset,2258+2*offset)
        checked['windows'].append((previous,previous,previous,previous,output));previous=output
        plans.append(dict(window_index=offset,writes=[2257+2*offset,2258+2*offset,51233+2*offset,51234+2*offset]))
    extracted=dict(identity=dict(schema='shieldd-transfer-relation-v1',relation_digest='a'*64,
        domain_size=262144,stored_rows=200770),selected_rows=[])
    return checked,extracted,plans


class ConstructorChunkTests(unittest.TestCase):
    def render(self,values):
        checked,selected,plans=values
        with patch.object(generator.completion,'window_plan',side_effect=plans), \
             patch.object(generator.joins,'actual_window_partition',return_value={}):
            return generator.generate(checked,selected)

    def test_small_certificates_reuse_symbolic_loop_and_exact_prior_rows(self):
        name,source=self.render(fixture(2))
        self.assertEqual(name,'RuntimeOwnershipConstructorChunk000')
        self.assertEqual(source.count('#check @'),7)
        self.assertEqual(source.count('#print axioms'),7)
        self.assertIn('GroupCircuitFrameTrace',source)
        self.assertIn('RuntimeOwnershipWindow000Program.priorRows',source)
        self.assertIn('RuntimeOwnershipWindow000Program.program (bits 250) (bits 251)',source)
        self.assertIn('RuntimeOwnershipWindow001Program.program (bits 248) (bits 249)',source)
        self.assertIn('GroupVariableCircuitCompletion.LocalConstruct',source)
        self.assertIn('original_rows_covered',source)
        self.assertIn('simp only [List.mem_cons,List.not_mem_nil,or_false] at named',source)
        self.assertIn('RuntimeOwnershipWindow000Program.original_rows_covered (bits 250) (bits 251)',source)
        self.assertIn('RuntimeOwnershipWindow001Program.original_rows_covered (bits 248) (bits 249)',source)
        self.assertNotIn('original_rows_covered _ _',source)
        self.assertNotIn('tauto',source)
        self.assertNotIn('native_decide',source)
        statement=source.split('theorem constructors',1)[1].split(' := by',1)[0]
        self.assertNotIn('Satisfies',statement)
        self.assertNotIn('Legal',statement)

    def test_gap_source_adjacency_or_protected_role_mutation_refuses(self):
        for mutation in ('gap','adjacency','low','randomizer','copy','table','bit','family'):
            values=copy.deepcopy(fixture(2));checked,selected,plans=values
            if mutation=='gap':plans[1]['writes'][-2]+=3
            elif mutation=='adjacency':checked['windows'][1]=(checked['windows'][0][0],*checked['windows'][1][1:])
            elif mutation=='low':plans[0]['writes'][0]=1980
            elif mutation=='randomizer':plans[0]['writes'].append(3766)
            elif mutation=='copy':plans[0]['writes'].append(200692)
            elif mutation=='table':checked['derived'][(1,1504)]=((3000,1),)
            elif mutation=='bit':checked['derived'][(1,2250)]=((3000,1),)
            else:checked['metadata']['schema']='pending'
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):self.render(values)


if __name__=='__main__':unittest.main()
