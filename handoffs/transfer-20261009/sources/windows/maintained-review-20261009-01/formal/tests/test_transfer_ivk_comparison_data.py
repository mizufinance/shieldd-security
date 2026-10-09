"""Unqualified source-emitter fixture; no observation or kernel result."""
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ivk_comparison_data as generator
from circuits.transfer_balance_rows import canonical,combine
from circuits.transfer_relation import MODULUS as P
from circuits.transfer_ivk_reduction import ORDER,TAIL


def fixture():
    raw={};roles={};phases=[];pivot=10000
    outline=lambda terms:canonical((60000 if c==0 else c,v) for c,v in terms)
    def add(left,right):
        index=len(raw);raw[index]=(outline(left),outline(right));return index
    for phase,key,width,start,bound in ((0,'quotient',4,1996,8),(1,'remainder',252,2000,ORDER-1),
                                       (2,'remainder',252,2000,TAIL-1)):
        steps=[];stages=[];before=((0,1),)
        for index in range(width):
            bit=((start+index,1),);flag=(bound>>index)&1
            if phase<2:roles[f'{key}.boolean.{index}']=add(bit,bit)
            factor=bit if flag else combine(((0,1),),bit,-1)
            if not index:product=factor
            else:
                product=((pivot,1),);aux=((pivot+1,1),);pivot+=2
                ids=[add(combine(before,factor,-1),aux),add(combine(before,factor),combine(aux,product,4))]
                stages.append(dict(left=before,right=factor,remainder=(),output=product[0][0],auxiliary=aux[0][0],rows=ids))
            after=combine(combine(product,((0,1),)),bit,-1) if flag else product
            steps.append(dict(before=before,left=bit,right=flag,factor=factor,product=product,after=after))
            before=after
        phases.append(dict(phase=phase,key=key,width=width,start=start,steps=steps,stages=stages))
    return dict(raw=raw,roles=roles,phases=phases,checked=dict(metadata=dict(constant_copy=60000)))


class ComparisonDataTests(unittest.TestCase):
    def test_shared_bits_and_bounded_certificates(self):
        plan=fixture()
        with patch.object(generator.reduction,'plan',return_value=plan):
            modules=list(generator.generate(b'fixture',{}, {},'0'*64))
        self.assertEqual(len(modules),33)
        self.assertTrue(all(source.count('#check @')==4 for _,source in modules))
        self.assertTrue(all('theorem endpoint_exact' in source and 'Satisfies' not in source for _,source in modules))
        first=plan['phases'][1];terminal=plan['phases'][2]
        self.assertEqual([step['left'] for step in first['steps']],[step['left'] for step in terminal['steps']])
        for n in (0,1,TAIL-1,TAIL,ORDER-1):
            rho={0:1,60000:1,**{2000+i:(n>>i)&1 for i in range(252)}}
            value=lambda terms:sum(rho.get(c,0)*v for c,v in terms)%P
            for phase in (first,terminal):
                for stage in phase['stages']:
                    left,right=value(stage['left']),value(stage['right'])
                    rho[stage['output']]=left*right%P
                    rho[stage['auxiliary']]=(left-right)**2%P
                endpoint=value(phase['steps'][-1]['after'])
                expected=int(n<=ORDER-1 if phase is first else n<=TAIL-1)
                self.assertEqual(endpoint,expected)
        # A terminal false outcome is legal; it must not be replaced by a
        # desired endpoint assertion in a constructor premise.
        self.assertGreater(ORDER-1,TAIL-1)


if __name__=='__main__':unittest.main()
