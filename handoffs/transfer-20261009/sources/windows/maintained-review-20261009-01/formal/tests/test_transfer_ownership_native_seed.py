"""Local native-reader seed fixtures; no runtime or kernel qualification."""
import copy,unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_native_seed as generator
from circuits.transfer_relation import RelationError
from tests.test_transfer_ownership_double_completion import fixture


class NativeSeedTests(unittest.TestCase):
    def render(self,values):
        checked,extracted,plan,cones=values
        with patch.object(generator.completion,'window_plan',return_value=plan), \
                patch.object(generator.completion.owner,'cone_certificates',return_value=cones):
            return generator.generate(checked,extracted)

    def test_native_coordinate_and_curve_are_derived(self):
        name,source=self.render(fixture())
        self.assertEqual(name,'RuntimeOwnershipWindow000Point0CompletionNativeSeed')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertIn('ShielddPointCoordinateSeed.coordinates',source)
        self.assertIn('model.onCurve',source)
        self.assertIn('two_nsmul,model.addition',source)
        statement=source.split('theorem native_double_complete',1)[1].split(' := by',1)[0]
        self.assertNotIn('(valid :',statement)
        self.assertNotIn('(coordinates :',statement)
        self.assertNotIn('Satisfies base',statement)
        self.assertIn('2 • upstream.embed (upstream.promote point)',statement)

    def test_exact_native_singletons_and_distinct_roles(self):
        for terms in (((1,2),),((1,1),(3,1)),((2,1),),((0,1),),((100,1),)):
            values=copy.deepcopy(fixture());values[3]['observations']['px']=('linear',terms)
            with self.subTest(terms=terms),self.assertRaises(RelationError):self.render(values)


if __name__=='__main__':unittest.main()
