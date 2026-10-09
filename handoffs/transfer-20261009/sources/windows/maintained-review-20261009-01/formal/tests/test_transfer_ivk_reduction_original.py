import copy,unittest
from unittest.mock import patch
from circuits import generate_transfer_ivk_reduction_original as original,transfer_relation as relation
from tests.test_transfer_ivk_reduction_order import fixture as order_fixture
from tests import test_transfer_ivk_reduction_join as join_tests


def fixture():
    plan=order_fixture();stage=plan['gate_stage'];copycol=plan['checked']['metadata']['constant_copy']
    outline=lambda terms:tuple((copycol if c==0 else c,v) for c,v in terms)
    for index,row in zip(stage['rows'],original.joins._stage_rows(stage)):
        plan['raw'][index]=tuple(outline(terms) for terms in row)
    join_tests.ReductionJoinTests().generate(plan) # Add the exact seven tail fixture rows.
    inverse=list(range(len(plan['raw']),len(plan['raw'])+3))
    for index in inverse:plan['raw'][index]=((),())
    plan['inverse']=dict(rows=inverse)
    return plan


class ReductionOriginalTests(unittest.TestCase):
    def generate(self,plan):
        with patch.object(original.reduction,'plan',return_value=plan):
            return list(original.generate(b'fixture',{}, {},'0'*64))

    def test_exact_original_union_and_constructed_truth(self):
        plan=fixture();modules=self.generate(plan)
        self.assertEqual(len(plan['raw']),1278)
        self.assertEqual(len(modules),35)
        self.assertEqual(sum(source.count('#check @') for _,source in modules),36)
        source=modules[-1][1]
        self.assertIn('parts.flatten ++ RuntimeTransferIvkReductionTailCompletion.rawRows',source)
        statement=source[source.index('theorem original_complete'):source.index(' :=',source.index('theorem original_complete'))]
        self.assertNotIn('Satisfies base',statement)
        self.assertNotIn('satisfied',statement)
        self.assertNotIn('inverse',source)

    def test_missing_physical_row_refused(self):
        plan=fixture();plan['raw'][max(plan['raw'])+1]=((),())
        with self.assertRaises(relation.RelationError):self.generate(plan)

    def test_numeric_assignment_satisfies_all1275_selected_rows(self):
        plan=fixture();order=original.reduction.reduction.ORDER
        for n in (0,order-1,8*order,relation.MODULUS-1):
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
                for index,(a,b) in plan['raw'].items():
                    if index not in plan['inverse']['rows']:
                        self.assertEqual(value(a)**2%relation.MODULUS,value(b),index)


if __name__=='__main__':unittest.main()
