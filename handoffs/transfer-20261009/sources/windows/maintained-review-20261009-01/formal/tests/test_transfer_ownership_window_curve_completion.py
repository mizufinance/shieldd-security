"""Typed whole-window boundary tests without runtime or kernel evidence."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_window_curve_completion as generator
from circuits.transfer_relation import RelationError
from tests.test_transfer_ownership_double_completion import fixture as double_fixture


def fixture():
    checked, extracted, plan, _ = double_fixture()
    checked['derived'] = {(1,column): ((column,1),) for column in range(1,80)}
    point = lambda x,y: (('source',(1,x)),('source',(1,y)))
    checked['windows'] = [None,(point(1,2),point(20,30),point(40,50),point(3,4),point(60,70))]
    template = plan['stages']; stages = []
    for offset in (0,20,40):
        for stage in copy.deepcopy(template):
            for column in ('quotient','product','auxiliary'):
                stage[column] += offset
            stages.append(stage)
    plan.update(window_index=1, protected=[0,100,1,2,3,4], stages=stages,
        point_groups=[dict(index=5+axis,kind=('double','double','add')[axis],
            material_end=2*axis,stage_end=2*axis+2) for axis in range(3)])
    return checked, extracted, plan


class WholeWindowTests(unittest.TestCase):
    def render(self, values, offset=1):
        checked, extracted, plan = values
        with patch.object(generator.completion, 'window_plan', return_value=plan):
            return generator.generate(checked, extracted, offset)

    def test_same_assignment_constructs_and_retains_all_components(self):
        name, source = self.render(fixture())
        self.assertEqual(name,'RuntimeOwnershipWindow001CurveCompletion')
        self.assertEqual(source.count('#check @'),3)
        self.assertEqual(source.count('#print axioms'),3)
        self.assertIn('GroupCircuitSequenceCompletion.preserves_rows',source)
        self.assertIn('Point7SelectorCompletion.material_curve',source)
        self.assertIn('Point5Completion.actual_point_complete',source)
        self.assertIn('Point6Completion.actual_point_complete',source)
        self.assertIn('Point7Completion.actual_point_complete',source)
        self.assertIn('def d : Int :=',source)
        self.assertIn('Point5Completion.actual_point_complete imaginary nonSquare imaginarySquare base one linked incoming',source)
        self.assertIn('Point6Completion.actual_point_complete imaginary nonSquare imaginarySquare (afterFirst base) firstOne firstLink secondIncoming',source)
        self.assertIn('Point7Completion.actual_point_complete imaginary nonSquare imaginarySquare (beforeAdd base) nextOne nextLink',source)
        self.assertEqual(source.count('change RuntimeOwnershipWindow001Point5Completion.completed base 100 ='),2)
        self.assertIn('change RuntimeOwnershipWindow001Point6Completion.completed (afterFirst base) 100 =',source)
        self.assertIn('change Satisfies (RuntimeOwnershipWindow001Point6Completion.completed (afterFirst base)) firstRows',source)
        self.assertEqual(source.count('eval,Int.cast_one,one_mul,add_zero]'),2)
        statement=source.split('theorem actual_window_complete',1)[1].split(' := by',1)[0]
        self.assertIn('incoming',statement)
        self.assertIn('lowValue',statement)
        self.assertIn('baseValid',statement)
        self.assertNotIn('Satisfies base',statement)
        self.assertNotIn('Legal',statement)
        self.assertNotIn('denominatorValue',statement)

    def test_refuses_nonactual_operation_order_or_output(self):
        for mutation in ('order','output','folded','index'):
            values=copy.deepcopy(fixture())
            if mutation=='order':values[2]['point_groups'].reverse()
            elif mutation=='output':values[2]['stages'][2]['quotient']=41
            elif mutation=='folded':values[2]['stages'][0]['kind']='linear'
            else:values[2]['window_index']=0
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):
                self.render(values)
        for offset in (True,-1,2):
            with self.subTest(offset=offset),self.assertRaises(RelationError):
                self.render(fixture(),offset)


if __name__=='__main__':
    unittest.main()
