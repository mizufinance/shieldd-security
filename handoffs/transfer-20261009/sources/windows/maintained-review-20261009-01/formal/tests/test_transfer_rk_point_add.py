"""Exact pinned Point.add row-shape fixtures, never runtime observations."""
import copy
import io
import json
import unittest
from circuits import transfer_rk_addition as rk, transfer_rk_point_add as point_add
from circuits import transfer_authorization_roles as roles, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from circuits.transfer_fixed_spend import D
from tests import test_transfer_rk_binding as binding_fixture


def fixture(change=None):
    rows=[];copy_column=1000
    outline=lambda lc:canonical((copy_column if c==0 else c,k) for c,k in lc)
    def row(a,b=()):
        rows.append(dict(row=len(rows),a=[[c,f'{k:064x}'] for c,k in canonical(a)],b=[[c,f'{k:064x}'] for c,k in canonical(b)]))
    def product(left,right,column,aux):
        out=((column,1),);row(outline(combine(left,right,-1)),[(aux,1)])
        row(outline(combine(left,right)),combine(((aux,1),),out,4));return out
    row([(0,1),(copy_column,-1)])
    xx=product(((4,1),),((420,1),),600,650)
    yy=product(((5,1),),((421,1),),601,651)
    xy=product(xx,yy,603,653)
    plus=combine(((0,1),),((603,D),));minus=combine(((0,1),),((603,D),),-1)
    denominator=product(plus,minus,604,654);inverse=((605,1),)
    inverse_product=product(inverse,denominator,606,655)
    row(outline(combine(inverse_product,((0,1),),-1)))
    cross0=product(((4,1),),((421,1),),607,656)
    cross1=product(((5,1),),((420,1),),608,657)
    adjusted_x=product(combine(cross0,cross1),minus,609,658)
    product(adjusted_x,inverse,422,659)
    adjusted_y=product(combine(yy,xx),plus,610,660)
    product(adjusted_y,inverse,423,661)
    if change:change(rows)
    for i,r in enumerate(rows):r['row']=i
    data,stream,digest,handles,rnk,ivk=binding_fixture.fixture(rows=rows)
    accepted=roles.inspect_metadata(data,digest,handles,rnk,ivk)
    return data,accepted,stream.getvalue()


class PointAddTests(unittest.TestCase):
    def test_exact_shared_inverse_and_json_replay(self):
        data,accepted,stream=fixture();e=rk.extract(data,accepted,lambda:io.BytesIO(stream))
        self.assertEqual(e['algorithm'],point_add.ALGORITHM);self.assertEqual(len(e['selected_rows']),24)
        self.assertEqual(e['intermediates']['inverse'],[[605,1]])
        self.assertEqual(e['intermediates']['outputX'],[[422,1]])
        source=rk.generate(data,accepted,json.loads(json.dumps(e)))
        for name in ('inverse_equation','actual_addition_affine','actual_addition_rows','actual_add_coordinates'):
            self.assertEqual(source.count('#check @'+name+'\n'),1)
        for forbidden in ('sorry','native_decide','admit'):self.assertNotIn(forbidden,source)
        self.assertNotIn('RuntimeTransferRkAdditionDiv',source)

    def test_missing_inverse_assertion_endpoint_and_duplicate_unit_pair_refuse(self):
        def inverse_assertion(rows):rows.pop(11)
        def endpoint(rows):rows[-1]['b'][0][1]=f'{8:064x}'
        def duplicate(rows):rows.extend(copy.deepcopy(rows[1:3]))
        for change in (inverse_assertion,endpoint,duplicate):
            data,a,stream=fixture(change)
            with self.subTest(change=change.__name__),self.assertRaises(relation.RelationError):
                rk.extract(data,a,lambda:io.BytesIO(stream))

    def test_second_coordinate_using_different_inverse_refuses(self):
        def change(rows):
            for row in rows[-2:]:
                for term in row['a']:
                    if term[0]==605:term[0]=612
                row['a'].sort()
        data,a,stream=fixture(change)
        with self.assertRaisesRegex(relation.RelationError,'shared inverse'):
            rk.extract(data,a,lambda:io.BytesIO(stream))

    def test_persisted_inverse_endpoint_and_extra_row_refuse(self):
        data,a,stream=fixture();e=rk.extract(data,a,lambda:io.BytesIO(stream))
        for name,value in (('inverse',[[612,1]]),('outputX',[[612,1]])):
            changed=copy.deepcopy(e);changed['intermediates'][name]=value
            with self.assertRaises(relation.RelationError):rk.generate(data,a,changed)
        changed=copy.deepcopy(e);changed['selected_rows'][-1]['b'][0][1]=f'{8:064x}'
        with self.assertRaises(relation.RelationError):rk.generate(data,a,changed)

    def test_constant_sum_cross_join_is_rejected_by_unit_shape(self):
        def unrelated(rows):
            rows.append(dict(row=0,a=[[1000,f'{2:064x}']],b=[[700,f'{4:064x}'],[701,f'{1:064x}']]))
        data,a,stream=fixture(unrelated)
        e=rk.extract(data,a,lambda:io.BytesIO(stream))
        self.assertEqual(len(e['selected_rows']),24)
        self.assertEqual(e['intermediates']['denominator'],[[604,1]])

    def test_mixed_constructor_covers_all_rows_and_has_no_satisfaction_premise(self):
        data,a,stream=fixture();e=rk.extract(data,a,lambda:io.BytesIO(stream))
        plan=rk.completion_plan(data,a,e)
        self.assertEqual(len(plan['stages']),11);self.assertEqual(len(plan['writes']),23)
        self.assertEqual(len(plan['original_rows']),24)
        self.assertFalse(set(plan['kept'])&set(plan['writes']))
        source=rk.generate_whole_completion(data,a,json.loads(json.dumps(e)))
        self.assertIn('Group.denominators_nonzero',source)
        self.assertIn('theorem emitted_exact',source)
        self.assertIn('theorem actual_addition_group_complete',source)
        self.assertNotIn('(satisfied :',source)

    def test_inverse_assertion_negative_orientation_has_explicit_transport(self):
        def change(rows):
            rows[11]['a']=[[c,f'{k:064x}'] for c,k in canonical((c,-int(k,16)) for c,k in rows[11]['a'])]
        data,a,stream=fixture(change);e=rk.extract(data,a,lambda:io.BytesIO(stream))
        plan=rk.completion_plan(data,a,e)
        self.assertTrue(plan['stages'][4]['assertion_negative'])
        source=rk.generate_whole_completion(data,a,e)
        self.assertIn('rcases left with positive | negative',source)
        self.assertIn('scaleLinear (-1) expected.a',source)

    def test_constructive_recipe_has_a_same_assignment_numeric_witness(self):
        # Independent field execution checks the recipe's nonvacuity and every
        # selected square row. This is a fixture test, not native verification.
        data,a,stream=fixture();e=rk.extract(data,a,lambda:io.BytesIO(stream))
        plan=rk.completion_plan(data,a,e);raw=rk._selection(data,a,e)[2];p=relation.MODULUS
        left=(3,26155723652191673091881779851507865815856437797311909079256717375290769542325)
        def add(x,y):
            delta=D*x[0]*y[0]*x[1]*y[1]%p;inverse=pow((1-delta*delta)%p,-1,p)
            return ((x[0]*y[1]+x[1]*y[0])*(1-delta)*inverse%p,(x[1]*y[1]+x[0]*y[0])*(1+delta)*inverse%p)
        right=add(left,left)
        for point in (left,right):self.assertEqual((point[1]**2-point[0]**2-1-D*point[0]**2*point[1]**2)%p,0)
        rho={0:1,1000:1,4:left[0],5:left[1],420:right[0],421:right[1],19:12345}
        before={c:rho.get(c,0) for c in plan['kept']}
        def evaluate(lc):return sum(k*rho.get(c,0) for c,k in lc)%p
        for s in plan['stages']:
            if s['kind']=='product':
                l,r,rem=(evaluate(s[k]) for k in ('left','right','remainder'))
                rho[s['output']]=(l*r-rem)%p;rho[s['auxiliary']]=(l-r)**2%p
            else:
                n,d,rem=(evaluate(s[k]) for k in ('numerator','denominator','remainder'))
                self.assertNotEqual(d,0);q=n*pow(d,-1,p)%p
                rho[s['quotient']]=q;rho[s['product']]=(q*d-rem)%p;rho[s['auxiliary']]=(q-d)**2%p
        self.assertEqual((rho[422],rho[423]),add(left,right))
        self.assertEqual({c:rho.get(c,0) for c in before},before)
        self.assertTrue(all(evaluate(x)**2%p==evaluate(y) for x,y in raw.values()))
        changed=dict(raw);index=sorted(raw)[-1];x,y=changed[index];changed[index]=(x,combine(y,((422,1),)))
        self.assertNotEqual(evaluate(changed[index][0])**2%p,evaluate(changed[index][1]))


if __name__=='__main__':unittest.main()
