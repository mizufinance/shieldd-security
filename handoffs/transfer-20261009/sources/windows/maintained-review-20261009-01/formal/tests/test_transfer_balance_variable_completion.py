"""Synthetic129 source/row tests; no actual capture or kernel credit."""
import copy,json,unittest
from unittest.mock import patch
from circuits import transfer_balance_variable as variable
from circuits import transfer_balance_variable_completion as completion
from circuits import transfer_relation as relation
from tests.test_transfer_balance_variable import fixture,balance_rows
from tests.transfer_ownership_fixture import symbolic_window


def accepted_fixture():
    metadata,signed,base=fixture()
    checked=variable.inspect_metadata((json.dumps(metadata)+'\n').encode(),'a'*64,signed,base)
    _,original=symbolic_window();rows=balance_rows(original['selected_rows'])
    def replay(stream,expected_relation,row_observer):
        for row in rows:row_observer(row)
        return dict(relation_digest='a'*64,domain_size=16384,stored_rows=metadata['full_rows'])
    with patch.object(variable.relation,'inspect',side_effect=replay):
        extracted=variable.extract_rows(checked,None,'a'*64)
    return checked,extracted


class BalanceVariableCompletionTests(unittest.TestCase):
    def test_constructed_owned_writes_satisfy_rows_and_preserve_shared_columns(self):
        checked,extracted=accepted_fixture();plan=completion.window_plan(checked,extracted)
        self.assertTrue({0,1,2,6,16000}<=set(plan['protected']))
        p=relation.MODULUS;d=-10240*pow(10241,-1,p)%p
        base=(3,26155723652191673091881779851507865815856437797311909079256717375290769542325)
        def add(a,b):
            x,y=a;u,v=b;t=d*x*y*u*v%p
            return ((x*v+y*u)*pow((1+t)%p,-1,p)%p,(x*u+y*v)*pow((1-t)%p,-1,p)%p)
        twice=add(base,base);triple=add(twice,base)
        self.assertEqual((base[1]**2-base[0]**2-1-d*base[0]**2*base[1]**2)%p,0)
        def evaluate(terms,rho):return sum(v*rho.get(c,0) for c,v in terms)%p
        for low,high in ((0,0),(1,0),(0,1),(1,1)):
            rho={0:1,16000:1}
            for value,n in zip(checked['points']['base'],base):rho[checked['derived'][value[1]][0][0]]=n
            for value,n in zip(checked['windows'][0][0],(0,1)):rho[checked['derived'][value[1]][0][0]]=n
            for value,n in zip(checked['window_bits'][0],(low,high)):rho[checked['derived'][value[1]][0][0]]=n
            before=dict(rho)
            for step in plan['stages']:
                if step['kind']=='square':
                    rho[step['output']]=(evaluate(step['input'],rho)**2-evaluate(step['remainder'],rho))%p
                elif step['kind']=='product':
                    left,right=evaluate(step['left'],rho),evaluate(step['right'],rho)
                    rho[step['output']]=(left*right-evaluate(step['remainder'],rho))%p
                    rho[step['auxiliary']]=(left-right)**2%p
                elif step['kind']=='quotient':
                    numerator,denominator=evaluate(step['numerator'],rho),evaluate(step['denominator'],rho)
                    self.assertNotEqual(denominator,0)
                    quotient=numerator*pow(denominator,-1,p)%p
                    rho[step['quotient']]=(quotient-evaluate(step['remainder'],rho))%p
                    rho[step['product']]=numerator;rho[step['auxiliary']]=(quotient-denominator)**2%p
                else:self.fail('fixture should exercise explicit square/product/quotient writes')
            chosen=((0,1),base,twice,triple)[low+2*high]
            actual=tuple(evaluate(checked['derived'][value[1]],rho) for value in checked['windows'][0][4])
            self.assertEqual(actual,chosen)
            for row in extracted['selected_rows']:
                if row['row'] not in plan['local_rows']:continue
                a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
                self.assertEqual(evaluate(a,rho)**2%p,evaluate(b,rho))
            self.assertTrue(all(rho.get(c,0)==before.get(c,0) for c in plan['protected']))
        pivot=plan['stages'][0]['output']
        with self.assertRaisesRegex(relation.RelationError,'aliases shared/prior support'):
            completion.window_plan(checked,extracted,readonly_lcs=(((pivot,1),),))

    def test_relocated_valid_product_cannot_write_original_asset_column(self):
        checked,extracted=accepted_fixture()
        pivot=completion.window_plan(checked,extracted)['stages'][0]['output']
        # Rename the actual polynomial/source-LC fixture consistently. It is
        # still a valid local materialization, but must preserve earlier asset6.
        for field in ('derived','expressions'):
            for handle,terms in list(checked[field].items()):
                checked[field][handle]=completion.canonical((6 if c==pivot else c,v) for c,v in terms)
        for expression in checked['metadata']['expressions']:
            expression['terms']=sorted([[6 if c==pivot else c,v] for c,v in expression['terms']])
        for row in extracted['selected_rows']:
            for key in ('a','b'):
                row[key]=sorted([[6 if c==pivot else c,v] for c,v in row[key]])
        with self.assertRaisesRegex(relation.RelationError,'aliases shared/prior support'):
            completion.window_plan(checked,extracted)

    def test129_uses_actual_pair_and_original_square_product_quotient_rows(self):
        checked,extracted=accepted_fixture()
        with patch.object(completion.ownership,'match_formulas',side_effect=AssertionError('252 matcher forbidden')):
            result=completion.cone_certificates(checked,extracted)
        self.assertEqual(len(result['cones']),22)
        self.assertEqual(len(result['quotients']['certificates']),10)
        self.assertEqual(result['metadata_sha256'],checked['metadata_sha256'])
        steps=completion.product_steps(result)['steps']
        self.assertTrue(steps)
        selected={r['row'] for r in extracted['selected_rows']}
        self.assertTrue(all(set(step['rows'])<=selected for step in steps))
        for step in steps:
            self.assertNotIn(step['output'],(0,16000))
        # The exact quotient checker refuses loss of its materialized numerator
        # assertion even when both quotient product rows remain available.
        original=next(c for c in result['quotients']['certificates'] if c['kind']=='product')
        damaged=copy.deepcopy(extracted)
        damaged['selected_rows']=[r for r in damaged['selected_rows'] if r['row']!=original['rows'][-1]]
        with self.assertRaises(relation.RelationError):completion.cone_certificates(checked,damaged)

    def test_numeric_orientation_duplicate_identity_and252_view_refuse(self):
        checked,extracted=accepted_fixture()
        result=completion.cone_certificates(checked,extracted)
        material=next(proof for cone in result['cones'] for proof in cone['certificates'].values()
                      if proof['kind']=='product')
        rowindex=material['rows'][0]
        damaged=copy.deepcopy(extracted)
        row=next(row for row in damaged['selected_rows'] if row['row']==rowindex)
        row['a'][0][1]=f'{(int(row["a"][0][1],16)+1)%relation.MODULUS:064x}'
        with self.assertRaises(relation.RelationError):completion.cone_certificates(checked,damaged)
        damaged=copy.deepcopy(extracted);damaged['selected_rows'].insert(1,copy.deepcopy(damaged['selected_rows'][0]))
        with self.assertRaises(relation.RelationError):completion.cone_certificates(checked,damaged)
        damaged=copy.deepcopy(extracted);damaged['identity']['relation_digest']='b'*64
        with self.assertRaises(relation.RelationError):completion.cone_certificates(checked,damaged)
        wrong=copy.deepcopy(checked);wrong['metadata']['bit_width']=252
        with self.assertRaises(relation.RelationError):completion.cone_certificates(wrong,extracted)


if __name__=='__main__':unittest.main()
