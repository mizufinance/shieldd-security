"""Finite row-algebra fixtures only; no runtime qualification or curve credit."""
import copy
import unittest
from circuits import transfer_balance_final_add as final, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine


def fixture():
    roles = dict(relation_digest=final.DIGEST, variable_parent='1'*64,
                 blinding_parent='2'*64, caller_parent='3'*64,
                 negative=((14,1),), unsigned=(((10,1),),((11,1),)),
                 blinded=(((12,1),),((13,1),)), output=(((160,1),),((161,1),)))
    rows = []
    def emit(a,b):
        outline = lambda lc: canonical((200692 if c == 0 else c,v) for c,v in lc)
        a,b = outline(a),outline(b)
        rows.append(dict(row=len(rows),a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b]))
    def product(left,right,col):
        out,aux = ((col,1),),((col+1,1),)
        emit(combine(left,right,-1),aux)
        emit(combine(left,right),combine(aux,out,4))
        return out
    sign = product(roles['negative'],((10,relation.MODULUS-2),),50)
    signed = (combine(roles['unsigned'][0],sign),roles['unsigned'][1])
    xx = product(signed[0],roles['blinded'][0],52)
    yy = product(signed[1],roles['blinded'][1],54)
    total = product(combine(*signed),combine(*roles['blinded']),56)
    xy = product(xx,yy,58)
    ns = (combine(combine(total,xx,-1),yy,-1),combine(yy,xx))
    dt = canonical((c,final.D*v) for c,v in xy)
    ds = (combine(final.ONE,dt),combine(final.ONE,dt,-1))
    for axis in range(2):
        out = product(roles['output'][axis],ds[axis],60+2*axis)
        emit(combine(out,ns[axis],-1),())
    rows.append(dict(row=len(rows),a=[[0,f'{1:064x}'],[200692,f'{relation.MODULUS-1:064x}']],b=[]))
    identity = dict(relation_digest=final.DIGEST,domain_size=262144,stored_rows=200770)
    return roles,rows,identity


class FinalBalanceTests(unittest.TestCase):
    def test_original_asset_id_is_protected_without_optional_readonly_inventory(self):
        roles,rows,identity=fixture()
        matcher=final.Matcher(roles)
        for row in rows:matcher.observe(row)
        self.assertIn(6,matcher.finish(identity)['protected'])
        # A physically valid local product may still alias the earlier asset
        # witness. The constructor must refuse even without an optional frame.
        changed=copy.deepcopy(rows)
        for row in changed:
            for key in ('a','b'):
                row[key]=sorted([[6 if column==50 else column,value] for column,value in row[key]])
        matcher=final.Matcher(roles)
        for row in changed:matcher.observe(row)
        with self.assertRaisesRegex(relation.RelationError,'writes alias shared'):
            matcher.finish(identity)

    def test_original_rows_construct_negative_zero_and_positive_values(self):
        roles,rows,identity = fixture()
        matcher = final.Matcher(roles)
        for row in rows: matcher.observe(row)
        plan = matcher.finish(identity,readonly_lcs=(((6,1),),))
        self.assertEqual(len(plan['stages']),7)
        self.assertEqual(len(plan['writes']),16)
        self.assertEqual(plan['selected_rows'],rows)
        self.assertTrue({0,1,2,6,10,11,12,13,14,200692}<=set(plan['protected']))
        for negative,x,y,bx,by in ((0,3,4,5,6),(1,3,4,5,6),(0,0,1,0,1)):
            rho = {0:1,200692:1,10:x,11:y,12:bx,13:by,14:negative}
            evaluate = lambda lc: sum(rho[c]*v for c,v in lc)%relation.MODULUS
            for stage in plan['stages']:
                if stage['kind']=='product':
                    left,right = stage['left'],stage['right']
                    rho[stage['output']] = (evaluate(left)*evaluate(right)-evaluate(stage['remainder']))%relation.MODULUS
                    rho[stage['auxiliary']] = (evaluate(left)-evaluate(right))**2%relation.MODULUS
                else:
                    n,d = evaluate(stage['numerator']),evaluate(stage['denominator'])
                    self.assertNotEqual(d,0)
                    q = n*pow(d,-1,relation.MODULUS)%relation.MODULUS
                    rho[stage['quotient']] = q
                    rho[stage['product']] = (q*d-evaluate(stage['remainder']))%relation.MODULUS
                    rho[stage['auxiliary']] = (q-d)**2%relation.MODULUS
            for row in rows:
                terms = [tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b')]
                self.assertEqual(evaluate(terms[0])**2%relation.MODULUS,evaluate(terms[1]))
            sx = (-x if negative else x)%relation.MODULUS
            den = final.D*sx*bx*y*by%relation.MODULUS
            self.assertEqual(rho[160],(sx*by+y*bx)*pow(1+den,-1,relation.MODULUS)%relation.MODULUS)
            self.assertEqual(rho[161],(y*by+sx*bx)*pow((1-den)%relation.MODULUS,-1,relation.MODULUS)%relation.MODULUS)

    def test_ambiguous_missing_wrong_assertion_and_readonly_alias_refuse(self):
        roles,rows,identity = fixture()
        for variant in ('missing','duplicate','assertion','readonly','order'):
            altered = copy.deepcopy(rows)
            if variant=='missing': altered.pop(3)
            if variant=='duplicate': altered.insert(2,copy.deepcopy(altered[0]))
            if variant=='assertion': altered[-2]['a'][0][1]=f'{2:064x}'
            if variant=='order': altered[:4]=altered[2:4]+altered[:2]
            for i,row in enumerate(altered): row['row']=i
            with self.subTest(variant=variant),self.assertRaises(relation.RelationError):
                matcher = final.Matcher(roles)
                for row in altered: matcher.observe(row)
                matcher.finish(identity,readonly_lcs=(((50,1),),) if variant=='readonly' else ())

    def test_closed_role_schema_and_original_identity_refuse(self):
        roles,rows,identity = fixture()
        for change in ('flag','parent','boolean','outline'):
            altered=copy.deepcopy(roles)
            if change=='flag': altered['ordinary_full_ordered_rows_equal']=True
            if change=='parent': altered['caller_parent']='unknown'
            if change=='boolean': altered['negative']=((True,1),)
            if change=='outline': altered['unsigned']=(((200692,1),),((11,1),))
            with self.subTest(change=change),self.assertRaises(relation.RelationError): final.Matcher(altered)
        matcher=final.Matcher(roles)
        for row in rows: matcher.observe(row)
        with self.assertRaises(relation.RelationError): matcher.finish(dict(identity,stored_rows=18))
        for readonly in ((((True,1),),),(((6,True),),),(((262144,1),),)):
            with self.assertRaises(relation.RelationError): matcher.finish(identity,readonly_lcs=readonly)

    def test_actual_ingress_refuses_before_reading_any_ordinary_bytes(self):
        class UnopenedStream:
            def readline(self): raise AssertionError('unqualified ordinary stream was touched')
        with self.assertRaises(relation.RelationError):
            final.extract_actual(UnopenedStream(),b'{}\n',[],b'{}\n',[],b'{}\n',b'{}\n',{}, {},[],[])
