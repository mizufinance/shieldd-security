import copy,re,unittest
from unittest.mock import patch
from circuits import generate_transfer_ivk_reduction_order as order,transfer_relation as relation
from circuits.transfer_balance_rows import combine
from tests.test_transfer_ivk_comparison_data import fixture as comparison_fixture


def fixture():
    plan=comparison_fixture()
    for phase in plan['phases']:
        phase['value']=((1994 if phase['phase']==0 else 1995,1),)
        phase['columns']=list(range(phase['start'],phase['start']+phase['width']))
    last=plan['phases'][2]['stages'][-1]['auxiliary']+1
    plan['gate_stage']=dict(left=((1999,1),),right=combine(((0,1),),plan['phases'][2]['steps'][-1]['after'],-1),
        remainder=(),output=last,auxiliary=last+1,rows=[len(plan['raw']),len(plan['raw'])+1])
    plan['readonly']=[0,3,1980,1981,1994,1995,3766,60000]
    plan['checked']['metadata']['value']=[1,0]
    plan['checked']['expressions']={(1,0):((3,1),)}
    return plan


class ReductionOrderTests(unittest.TestCase):
    def generate(self,plan):
        with patch.object(order.reduction,'plan',return_value=plan):
            return order.generate(b'fixture',{}, {},'0'*64)

    def test_symbolic506_products_and_shared_bit_initialization(self):
        _,source=self.generate(fixture())
        bodies=re.findall(r'def chunk[0-9]{3} : List CompilerCompletion.Step := \[(.*?)\]\n',source,re.S)
        counts=[body.count('.product ') for body in bodies]
        self.assertEqual(len(counts),34)
        self.assertEqual(sum(counts),506)
        self.assertLessEqual(max(counts),16)
        self.assertEqual(source.count('#check @'),4)
        statement=source[source.index('theorem constructs'):source.index(' :=',source.index('theorem constructs'))]
        self.assertNotIn('satisfied',statement)
        self.assertNotIn('meaning',statement)
        self.assertIn('ScalarReductionSeed.products_constructed',source)

    def test_write_order_and_owned_seed_collisions_refuse(self):
        for mutant in ('order','seed'):
            plan=copy.deepcopy(fixture())
            if mutant=='order':plan['phases'][1]['stages'][0]['output']=1
            else:plan['readonly'].append(2000)
            with self.subTest(mutant=mutant),self.assertRaises(relation.RelationError):self.generate(plan)


if __name__=='__main__':unittest.main()
