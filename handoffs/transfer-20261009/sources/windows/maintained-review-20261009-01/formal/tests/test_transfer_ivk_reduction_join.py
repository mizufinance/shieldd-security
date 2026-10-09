"""Typed source-only certificates; no runtime observation or kernel claim."""
import copy,re,unittest
from unittest.mock import patch
from circuits import generate_transfer_ivk_reduction_join as join,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_ivk_reduction_order import fixture


class ReductionJoinTests(unittest.TestCase):
    def generate(self,plan):
        copycol=plan['checked']['metadata']['constant_copy']
        def row(role,left):
            index=len(plan['raw']);plan['roles'][role]=index
            plan['raw'][index]=(canonical((copycol if c==0 else c,v) for c,v in left),())
        for phase in plan['phases'][:2]:
            row(phase['key']+'.reconstruction',combine([(phase['start']+i,2**i) for i in range(phase['width'])],phase['value'],-1))
            row(phase['key']+'_end.assertion',combine(phase['steps'][-1]['after'],((0,1),),-1))
        row('hash-equation',combine(((1994,join.reduction.reduction.ORDER),(1995,1)),((3,1),),-1))
        row('terminal-gate',((plan['gate_stage']['output'],1),))
        # This link is deliberately unoutlined, as in the actual full stream.
        index=len(plan['raw']);plan['roles']['constant-copy']=index
        plan['raw'][index]=(canonical([(0,1),(copycol,-1)]),())
        with patch.object(join.reduction,'plan',return_value=plan):
            return list(join.generate(b'fixture',{}, {},'0'*64))

    def test_bounded_canonical_transport_same_assignment(self):
        modules=self.generate(fixture())
        self.assertEqual(len(modules),38)
        self.assertEqual(sum(source.count('#check @') for _,source in modules),163)
        sources=dict(modules)
        for name,source in modules:
            self.assertNotIn('namespace O :=',source)
            self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
            self.assertNotIn('(satisfied :',source)
        first=sources['RuntimeTransferIvkComparison1RowJoinChunk0']
        later=sources['RuntimeTransferIvkComparison1RowJoinChunk1']
        self.assertIn('emitted RuntimeTransferIvkReductionProductOrder.chunk001',first)
        self.assertNotIn('chunk002',first)
        self.assertIn('emitted RuntimeTransferIvkReductionProductOrder.chunk001',later)
        self.assertIn('emitted RuntimeTransferIvkReductionProductOrder.chunk002',later)
        self.assertIn('List.range\' 2016 16',later)
        terminal=sources['RuntimeTransferIvkComparison2Common']
        for phase in range(3):
            common=sources[f'RuntimeTransferIvkComparison{phase}Common']
            self.assertIn('exact True.intro',common)
            self.assertIn(',True.intro⟩',common)
        self.assertIn('List.range\' 2000 252',terminal)
        self.assertIn('TransferReduction.endpoint_append',terminal)
        self.assertIn('ScalarChunkComposition.chunks_certificate',terminal)
        # No full1270-row decide walk: only <=80-row local Data transports.
        self.assertTrue(all('checkRow Scalar.modulus boundedRows' in source
            for name,source in modules if 'RowJoinChunk' in name))
        endpoint=sources['RuntimeTransferIvkReductionEndpoints']
        self.assertIn('ScalarReductionCompletion.decoded_operands',endpoint)
        self.assertIn('ScalarReductionAssertions.gate_zero',endpoint)
        self.assertIn('ScalarReductionSupport.hash_preserved',endpoint)
        self.assertNotIn('(bound :',endpoint)
        # Establish bounds on the exact Seed aliases before arithmetic; the
        # endpoint's if condition uses the captured comparator maximum literal.
        self.assertIn('have operandBound : ScalarReductionSeed.quotient',endpoint)
        self.assertIn('have operandBound : ScalarReductionSeed.remainder',endpoint)
        self.assertIn(f'≤ {join.reduction.reduction.ORDER-1} := by',endpoint)
        self.assertIn('if_pos (show 1996 ≤ 1996+3 ∧ 1996+3 < 1996+4 from by decide)',endpoint)
        self.assertIn('change eval (RuntimeTransferIvkReductionProductOrder.construct codec base)',endpoint)
        self.assertNotIn('have bound := (ScalarReductionCompletion.decoded_operands',endpoint)
        tail=sources['RuntimeTransferIvkReductionTailCompletion']
        self.assertIn('(by exact List.mem_cons_self)',tail)
        self.assertIn('List.mem_cons_of_mem _ List.mem_cons_self',tail)
        self.assertNotIn('exact Or.inl rfl',tail)
        self.assertRegex(tail,r'change eval \(RuntimeTransferIvkReductionProductOrder.construct codec base\) .* = 1 at qEndpoint')
        self.assertRegex(tail,r'change eval \(RuntimeTransferIvkReductionProductOrder.construct codec base\) .* = 1 at rEndpoint')

    def test_retained_row_mutation_refused(self):
        plan=fixture();phase=plan['phases'][1]
        index=phase['stages'][16]['rows'][1]
        left,right=plan['raw'][index]
        plan['raw'][index]=(left,((1,1),))
        with self.assertRaises(relation.RelationError):self.generate(plan)

    def test_inventory_width_refused(self):
        plan=fixture();plan['phases'][1]['stages'].pop()
        with self.assertRaises(relation.RelationError):self.generate(plan)

    def test_euclidean_seed_satisfies_original_tail_in_both_terminal_branches(self):
        plan=fixture();self.generate(plan) # Creates the fixture's exact tail7.
        order=join.reduction.reduction.ORDER
        for n in (0,1,order-1,8*order,relation.MODULUS-1):
            with self.subTest(n=n):
                q,r=divmod(n,order)
                rho={0:1,60000:1,3:n,1994:q,1995:r}
                rho.update({1996+i:(q>>i)&1 for i in range(4)})
                rho.update({2000+i:(r>>i)&1 for i in range(252)})
                value=lambda terms:sum(rho.get(c,0)*v for c,v in terms)%relation.MODULUS
                for stages in [*(phase['stages'] for phase in plan['phases']),[plan['gate_stage']]]:
                    for stage in stages:
                        left,right,remainder=(value(stage[key]) for key in ('left','right','remainder'))
                        rho[stage['output']]=(left*right-remainder)%relation.MODULUS
                        rho[stage['auxiliary']]=(left-right)**2%relation.MODULUS
                for role in ('quotient.reconstruction','remainder.reconstruction','quotient_end.assertion',
                             'remainder_end.assertion','hash-equation','terminal-gate','constant-copy'):
                    a,b=plan['raw'][plan['roles'][role]]
                    self.assertEqual(value(a)**2%relation.MODULUS,value(b),role)
                self.assertEqual(value(plan['phases'][2]['steps'][-1]['after']),int(r<=join.reduction.reduction.TAIL-1))
                self.assertEqual(rho[plan['gate_stage']['output']],0)


if __name__=='__main__':unittest.main()
