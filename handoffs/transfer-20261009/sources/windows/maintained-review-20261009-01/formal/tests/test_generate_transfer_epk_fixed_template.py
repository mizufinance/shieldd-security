"""Small mathematical renderer fixtures; no captured EPK or kernel credit."""
import copy,re,unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template as emit
from circuits import transfer_fixed_spend as fixed,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_fixed_spend_rows import curve_fixture


def fixture():
    low,high=((11,1),),((12,1),)
    before=(((30,1),),((31,1),));selected=(((40,1),),((41,1),))
    base=curve_fixture();twice=fixed._add(base,base);triple=fixed._add(twice,base)
    table=(base,twice,triple,fixed._add(twice,twice))
    lo=[canonical((c,v*base[0]) for c,v in low),combine(((0,1),),canonical((c,v*(base[1]-1)) for c,v in low))]
    hi=[combine(((0,twice[axis]),),canonical((c,v*(triple[axis]-twice[axis])) for c,v in low)) for axis in range(2)]
    values=[((50+i,1),) for i in range(4)]
    inputs=[(high,combine(hi[i],lo[i],-1),combine(selected[i],lo[i],-1)) for i in range(2)]
    inputs += [(before[0],selected[0],values[0]),(before[1],selected[1],values[1]),
               (combine(*before),combine(*selected),values[2]),(values[0],values[1],values[3])]
    raw={0:(canonical([(0,1),(1000,-1)]),()),1:(low,low),2:(high,high)}
    stages=[]
    for i,(left,right,result) in enumerate(inputs):
        output=40+i if i<2 else 48+i;auxiliary=201+2*i
        remainder=canonical((c,v) for c,v in result if c!=output)
        start=3+2*i
        raw[start]=(combine(left,right,-1),((auxiliary,1),))
        raw[start+1]=(combine(left,right),combine(((auxiliary,1),),result,4))
        stages.append(dict(kind='product',left=left,right=right,remainder=remainder,
                           output=output,auxiliary=auxiliary,rows=[start,start+1]))
    for axis in range(2):
        numerator=(combine(combine(values[2],values[0],-1),values[1],-1) if axis==0 else combine(values[1],values[0]))
        denominator=combine(((0,1),),canonical((c,v*fixed.D) for c,v in values[3]),1 if axis==0 else -1)
        quotient,product,auxiliary=60+axis,62+axis,214+axis
        start=15+3*axis
        raw[start]=(combine(((quotient,1),),denominator,-1),((auxiliary,1),))
        raw[start+1]=(combine(((quotient,1),),denominator),((auxiliary,1),(product,4)))
        raw[start+2]=(combine(((product,1),),numerator,-1),())
        stages.append(dict(kind='quotient',numerator=numerator,denominator=denominator,remainder=(),
                           quotient=quotient,product=product,auxiliary=auxiliary,rows=[start,start+1,start+2]))
    observed={(1,8):low,(1,9):high}
    checked=dict(points=[(before,selected,(((60,1),),((61,1),)))],tables=[table],
        metadata={'constant_copy':1000,'bits':[[1,6],[1,7],[1,8],[1,9]]},observed=observed,
        products=[(f'window.1.{name}',*inputs[i]) for i,name in enumerate(('select.0','select.1','xx','yy','sum','xy'))])
    plan=dict(window_count=1,windows=[dict(index=1,stages=stages)],kept=[0,1,2,11,12,30,31,1000],initial_rows=[0,1,2])
    return checked,raw,copy.deepcopy(raw),plan


class EpkFixedTemplateTests(unittest.TestCase):
    def test_small_adapter_exports_and_exact_physical_inventory(self):
        checked,raw,normalized,plan=fixture()
        source=emit.render_checked(checked,raw,normalized,plan,stem='FixtureEpkWindow001')
        self.assertIn('def originalRows : List Nat := '+str(sorted(raw)),source)
        self.assertIn('GroupFixedWindowTemplate.construct_complete',source)
        self.assertEqual(re.findall(r'^#print axioms (.+)$',source,re.M),[
            'checked_products','actual_window_complete'])
        self.assertEqual(len(re.findall(r'^set_option pp.all true in$',source,re.M)),2)
        signature=source[source.index('theorem actual_window_complete'):source.index(':= by',source.index('theorem actual_window_complete'))]
        self.assertNotIn('satisfied',signature)
        self.assertNotIn('Satisfies base',signature)
        self.assertNotIn('denominator',signature)

    def test_prod_entry_reuses_strict_epk_ingress_once(self):
        checked,raw,normalized,plan=fixture()
        selected=(checked,raw,normalized,{}, {},plan,'FixtureEpkWindow001')
        with patch.object(emit.ingress,'_selection',return_value=selected) as accept:
            source=emit.generate_window(b'parent',[],{}, {},{},0,0,0,readonly_lcs=(((7,1),),))
        accept.assert_called_once_with(b'parent',[],{}, {},{},0,0,0,(((7,1),),))
        self.assertIn('namespace ShielddSecurity.FixtureEpkWindow001TemplateCompletion',source)

    def test_folded_or_mixed_boundary_refuses(self):
        for mutation in ('first','kind','offset'):
            checked,raw,normalized,plan=fixture()
            if mutation=='first':plan['windows'][0]['index']=0
            elif mutation=='kind':plan['windows'][0]['stages'][5]['kind']='linear'
            with self.subTest(mutation=mutation),self.assertRaises(relation.RelationError):
                emit.render_checked(checked,raw,normalized,plan,True if mutation=='offset' else 0,stem='Fixture')

    def test_alias_and_duplicate_physical_roles_refuse(self):
        for mutation in ('write','bit','copy'):
            checked,raw,normalized,plan=fixture()
            if mutation=='write':plan['kept'].append(40)
            elif mutation=='bit':normalized[900]=normalized[1]
            else:raw[901]=raw[0]
            with self.subTest(mutation=mutation),self.assertRaises(relation.RelationError):
                emit.render_checked(checked,raw,normalized,plan,stem='Fixture')

    def test_prior_raw_support_is_part_of_same_protected_frame(self):
        checked,raw,normalized,plan=fixture()
        normalized[950]=(((777,1),),());plan['initial_rows'].append(950)
        layout=emit._layout(checked,raw,normalized,plan,0)
        self.assertIn(777,layout['kept'])
        self.assertNotIn(950,layout['used'])

if __name__=='__main__':unittest.main()
