"""Typed selector/linear-output joins, without runtime/kernel credit."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_folded_window_curve as generator
from circuits.transfer_relation import RelationError


def fixture():
    derived = {(1, i): ((i, 1),) for i in range(1, 253)}
    derived[(1, 90)] = ((70, 1),)
    derived[(1, 91)] = ((0, 1), (71, 1))
    point = lambda x,y: (('source',(1,x)),('source',(1,y)))
    checked = dict(metadata=dict(constant_copy=500), derived=derived,
                   points=dict(base=point(1,2),twice=point(3,4),triple=point(5,6)),
                   bits=[(1,i) for i in range(1,253)],
                   windows=[(None,None,None,point(90,91),point(100,101))])
    terms = [derived[(1,i)] for i in (1,2,3,4,5,6,251,252)]
    observations = {str(i): ('linear',value) for i,value in enumerate(terms)}
    observations.update(sx=('linear',derived[(1,90)]),sy=('linear',derived[(1,91)]))
    cones = dict(observations=observations,cones=[dict(role='formula'+str(20+i),inputs=list(map(str,range(8))),
                                                   output=('sx','sy')[i]) for i in range(2)])
    plan = dict(point_groups=[None,None,dict(material_end=0,stage_end=2)],
                stages=[dict(kind='linear',input=derived[(1,90+i)],remainder=(),output=100+i,rows=[i]) for i in range(2)])
    return checked,{},plan,cones


class FoldedCurveTests(unittest.TestCase):
    def render(self, values):
        checked,extracted,plan,cones = values
        with patch.object(generator.folded,'generate',return_value=('RuntimeOwnershipWindow000FoldedCompletion','')), \
                patch.object(generator.completion,'window_plan',return_value=plan), \
                patch.object(generator.completion.owner,'cone_certificates',return_value=cones):
            return generator.generate(checked,extracted)

    def test_constructed_selector_output_and_outgoing_curve(self):
        name,source = self.render(fixture())
        self.assertEqual(name,'RuntimeOwnershipWindow000FoldedCurveCompletion')
        self.assertEqual(source.count('#check @'),4)
        self.assertIn('Group.window_onCurve',source)
        self.assertIn('formula20_constructed',source)
        self.assertIn('formula21_constructed',source)
        statement = source.split('theorem actual_window_complete',1)[1].split(' := by',1)[0]
        self.assertNotIn('Satisfies base',statement)
        self.assertNotIn('denominator',statement)
        self.assertIn('baseValid',statement)
        self.assertIn('lowValue',statement)

    def test_exact_role_order_and_linear_output_required(self):
        for mutation in ('order','output','remainder','numerator','selected'):
            values=copy.deepcopy(fixture())
            if mutation=='order':values[3]['cones'][1]['inputs'].reverse()
            elif mutation=='output':values[2]['stages'][0]['output']=102
            elif mutation=='remainder':values[2]['stages'][0]['remainder']=((6,1),)
            elif mutation=='numerator':values[2]['stages'][0]['input']=((7,1),)
            else:values[3]['observations']['sx']=('linear',((70,2),))
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):self.render(values)


if __name__=='__main__':unittest.main()
