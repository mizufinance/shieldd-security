"""Finite symbolic source fixtures only; no runtime or kernel qualification."""
import re,unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template_program as emit
from circuits.transfer_relation import RelationError
from tests.test_generate_transfer_epk_fixed_template import fixture

class EpkTemplateProgramTests(unittest.TestCase):
    def test_full_named_module_order_and_exact_quotient_point(self):
        checked,raw,normal,plan=fixture()
        selected=(checked,raw,normal,{}, {},plan,'FixtureEpkWindow001')
        with patch.object(emit.ingress,'_selection',return_value=selected) as accept:
            modules=emit.generate_modules(b'parent',[],{}, {},{},0,0,0)
        accept.assert_called_once()
        self.assertEqual([name for name,_ in modules],[
            'FixtureEpkWindow001TemplateCompletion','FixtureEpkWindow001TemplateProgram'])
        source=modules[1][1]
        self.assertIn('GroupFixedWindowProgramTemplate.mixed_run',source)
        self.assertIn('output := ([(60, (1 : Int))],[(61, (1 : Int))])',source)
        self.assertEqual(re.findall(r'^#print axioms (.+)$',source,re.M),['local_constructor','original_rows'])
        self.assertEqual(source.count('set_option pp.all true in'),2)
        self.assertNotRegex(source,r'namespace \w+ :=')
        signature=source[source.index('theorem local_constructor'):source.index(':= by',source.index('theorem local_constructor'))]
        self.assertNotIn('Satisfies',signature)

    def test_different_or_scaled_output_lc_refuses(self):
        for endpoint in (((60,2),),((800,1),),((60,1),(61,1))):
            checked,raw,normal,plan=fixture()
            before,selected,after=checked['points'][0]
            checked['points'][0]=(before,selected,(endpoint,after[1]))
            with self.subTest(endpoint=endpoint),self.assertRaises(RelationError):
                emit.render_checked(checked,raw,normal,plan,stem='Fixture')

    def test_folded_window_refuses(self):
        checked,raw,normal,plan=fixture();plan['windows'][0]['index']=0
        with self.assertRaises(RelationError):
            emit.render_checked(checked,raw,normal,plan,stem='Fixture')

if __name__=='__main__':unittest.main()
