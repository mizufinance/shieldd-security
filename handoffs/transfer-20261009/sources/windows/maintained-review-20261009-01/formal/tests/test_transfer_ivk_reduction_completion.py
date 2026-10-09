import unittest
from circuits import generate_transfer_ivk_reduction_completion as generator,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine


def fixture(count=16):
    raw={};stages=[];left=((3,1),);right=((4,1),)
    for index in range(count):
        output,aux=100+2*index,101+2*index;ids=[2*index,2*index+1]
        raw[ids[0]]=(combine(left,right,-1),((aux,1),))
        raw[ids[1]]=(combine(left,right),((aux,1),(output,4)))
        raw[ids[1]]=(raw[ids[1]][0],canonical(raw[ids[1]][1]))
        stages.append(dict(left=left,right=right,remainder=(),output=output,auxiliary=aux,rows=ids))
        left=((output,1),)
    return dict(checked=dict(metadata=dict(constant_copy=5000)),readonly=[0,3,4,5000],raw=raw),stages


class ReductionConstructionTests(unittest.TestCase):
    def test_real_two_write_formula_satisfies_all_chunk_rows(self):
        plan,stages=fixture();rho={0:1,3:7,4:11,5000:1}
        value=lambda terms:sum(rho.get(c,0)*v for c,v in terms)%relation.MODULUS
        for stage in stages:
            l,r,rem=(value(stage[k]) for k in ('left','right','remainder'))
            rho[stage['output']]=(l*r-rem)%relation.MODULUS
            rho[stage['auxiliary']]=(l-r)**2%relation.MODULUS
        self.assertTrue(all(value(a)**2%relation.MODULUS==value(b) for a,b in plan['raw'].values()))
        _,source=generator._product_chunk(plan,'DiagnosticReduction',stages)
        self.assertEqual(source.count('#check @'),6)
        self.assertNotIn('satisfied',source[source.index('theorem complete'):source.index(' :=',source.index('theorem complete'))])
        with self.assertRaises(relation.RelationError):generator._product_chunk(plan,'Diagnostic',stages+[stages[0]])

    def test_inverse_retains_reversed_assertion_and_legal_denominator(self):
        q,p,a=7,100,101;consumer=((3,1),)
        raw={0:(combine(((q,1),),consumer,-1),((a,1),)),
            1:(combine(((q,1),),consumer),canonical([(a,1),(p,4)])),
            2:(canonical([(0,1),(p,-1)]),())}
        plan=dict(checked=dict(metadata=dict(constant_copy=5000)),raw=raw,
            inverse=dict(quotient=q,product=p,auxiliary=a,numerator=((0,1),),denominator=consumer,remainder=(),
                rows=[0,1,2],assertion_reversed=True))
        _,source=generator._inverse(plan)
        self.assertIn('scaleLinear (-1) expected.a',source)
        self.assertEqual(source.count('#check @'),4)
        rho={0:1,3:11,q:pow(11,-1,relation.MODULUS),p:1,5000:1}
        rho[a]=(rho[q]-rho[3])**2%relation.MODULUS
        value=lambda terms:sum(rho.get(c,0)*v for c,v in terms)%relation.MODULUS
        self.assertTrue(all(value(left)**2%relation.MODULUS==value(right) for left,right in raw.values()))
        # Zero denominator is an actual failed assertion, not an accepted
        # completeness witness: materialized product must equal one.
        rho.update({3:0,q:0,p:0,a:0})
        failures=[i for i,(left,right) in raw.items() if value(left)**2%relation.MODULUS!=value(right)]
        self.assertEqual(failures,[2])


if __name__=='__main__':unittest.main()
