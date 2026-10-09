"""Typed local double fixtures; no actual observer or kernel credit."""
import copy,unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_double_completion as generator
from circuits.transfer_balance_rows import canonical,combine
from circuits.transfer_relation import MODULUS,RelationError


def fixture():
    polynomials=[canonical([(10,-1),(11,-1),(12,1)]),canonical([(10,1),(11,1)]),
                 canonical([(10,-1),(11,1)]),canonical([(0,2),(10,1),(11,-1)])]
    observations=dict(px=('linear',((1,1),)),py=('linear',((2,1),)))
    cones=[]
    for index,terms in enumerate(polynomials):
        output='out'+str(index);observations[output]=('linear',terms)
        cones.append(dict(role='formula'+str(index),inputs=['px','py'],output=output))
    stages=[];raw=[]
    for axis,(numerator,denominator) in enumerate(((polynomials[0],polynomials[2]),(polynomials[1],polynomials[3]))):
        q,product,aux=20+10*axis,21+10*axis,22+10*axis
        first=1+3*axis
        stages.append(dict(kind='quotient',numerator=numerator,denominator=denominator,remainder=(),
                           quotient=q,product=product,auxiliary=aux,rows=[first,first+1,first+2]))
        pairs=[(combine([(q,1)],denominator,-1),((aux,1),)),
               (combine([(q,1)],denominator),canonical([(aux,1),(product,4)])),
               (combine([(product,1)],numerator,-1),())]
        for index,(a,b) in enumerate(pairs,first):
            encode=lambda terms:[[100 if column==0 else column,f'{coefficient%MODULUS:064x}']
                                 for column,coefficient in terms]
            raw.append(dict(row=index,a=encode(a),b=encode(b)))
    checked=dict(metadata=dict(constant_copy=100))
    plan=dict(window_index=0,point_groups=[dict(index=0,kind='double',material_end=0,stage_end=2)],stages=stages)
    return checked,dict(selected_rows=raw),plan,dict(cones=cones,observations=observations)


class DoubleCompletionTests(unittest.TestCase):
    def render(self,values):
        checked,extracted,plan,cones=values
        with patch.object(generator.completion,'window_plan',return_value=plan), \
                patch.object(generator.completion.owner,'cone_certificates',return_value=cones):
            return generator.generate(checked,extracted)

    def test_constructs_rows_and_curve_from_independent_input(self):
        name,source=self.render(fixture())
        self.assertEqual(name,'RuntimeOwnershipWindow000Point0Completion')
        self.assertEqual(source.count('#check @'),7)
        self.assertEqual(source.count('#print axioms'),7)
        self.assertIn('GroupQuotientPairCompletion.double_complete',source)
        self.assertIn('Compiler.canonical_equal',source)
        self.assertIn('GroupExtended.optimized_double_sound',source)
        self.assertIn('simp only [inputPoint,inputX,inputY,',source)
        statement=source.split('theorem actual_point_complete',1)[1].split(' := by',1)[0]
        self.assertIn('Group.OnCurve',statement)
        self.assertIn('(inputPoint base)',statement)
        self.assertNotIn('Legal',statement)
        self.assertNotIn('Satisfies base',statement)
        self.assertNotIn('denominatorValue',statement)

    def test_exact_formula_and_shared_input_order_required(self):
        for mutation in ('numerator','denominator','input_order','input_extra','coordinate_count','folded'):
            values=copy.deepcopy(fixture());plan=values[2];cones=values[3]
            if mutation in ('numerator','denominator'):plan['stages'][0][mutation]=((10,2),)
            elif mutation=='input_order':cones['cones'][2]['inputs'].reverse()
            elif mutation=='input_extra':cones['cones'][2]['inputs'].append('px')
            elif mutation=='coordinate_count':plan['stages'].pop()
            else:plan['stages'][0]['kind']='linear'
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):self.render(values)

    def test_later_window_double_reuses_actual_operation_roles(self):
        checked,extracted,plan,cones=fixture()
        checked['windows']=[None,None]
        plan['window_index']=1
        plan['point_groups'][0].update(index=5,formula_start=22)
        for index,cone in enumerate(cones['cones'],22):cone['role']='formula'+str(index)
        with patch.object(generator.completion,'window_plan',return_value=plan), \
                patch.object(generator.completion.owner,'cone_certificates',return_value=cones):
            name,source=generator.generate_window_double(checked,extracted,1,0)
            self.assertEqual(name,'RuntimeOwnershipWindow001Point5Completion')
            self.assertIn('formula22_constructed',source)
            self.assertIn('formula25_constructed',source)
            self.assertEqual(source.count('#check @'),7)
            for offset,axis in ((True,0),(2,0),(1,True),(1,2)):
                with self.assertRaises(RelationError):generator.generate_window_double(checked,extracted,offset,axis)


if __name__=='__main__':unittest.main()
