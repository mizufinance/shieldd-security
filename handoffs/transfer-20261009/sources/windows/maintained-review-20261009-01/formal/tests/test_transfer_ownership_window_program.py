"""Typed finite program fences; no runtime/kernel evidence from fixtures."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_window_program as generator
from circuits.transfer_relation import RelationError
from tests.test_transfer_ownership_window_curve_completion import fixture as window_fixture


def fixture():
    checked, extracted, plan = window_fixture()
    point = lambda x,y: (('source',(1,x)),('source',(1,y)))
    checked['points'] = dict(base=point(1,2),twice=point(20,30),triple=point(40,50))
    plan['writes'] = [20,30,40,50,60,70,51200,51201,51202]
    return checked, extracted, plan


class WindowProgramTests(unittest.TestCase):
    def render(self,values,offset=1):
        checked,extracted,plan=values
        with patch.object(generator.completion,'window_plan',return_value=plan):
            return generator.generate(checked,extracted,offset)

    def test_adapter_derives_rows_from_constructor_and_exact_fences(self):
        name,source=self.render(fixture())
        self.assertEqual(name,'RuntimeOwnershipWindow001Program')
        self.assertEqual(source.count('#check @'),4)
        self.assertIn('theorem original_rows_covered',source)
        self.assertIn('def beforeFrame : GroupFixedCircuitBounds.Frame := ⟨20,51200⟩',source)
        self.assertIn('def afterFrame : GroupFixedCircuitBounds.Frame := ⟨71,51203⟩',source)
        self.assertIn('GroupFixedCircuitBounds.checkLocal 22738 100',source)
        self.assertIn('GroupVariableCircuitCompletion.LocalConstruct',source)
        self.assertIn('CurveCompletion.actual_window_complete',source)
        self.assertIn('curved.1 curved.2.1 curved.2.2',source)
        statement=source.split('theorem local_constructor',1)[1].split(' := by',1)[0]
        self.assertNotIn('Satisfies',statement)
        self.assertNotIn('Legal',statement)

    def test_fences_refuse_duplicate_or_missing_owned_band(self):
        for mutation in ('duplicate','low','high'):
            values=copy.deepcopy(fixture())
            if mutation=='duplicate':values[2]['writes'].append(20)
            elif mutation=='low':values[2]['writes']=[51200,51201]
            else:values[2]['writes']=[20,30]
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):
                self.render(values)
        for offset in (True,-1,2):
            with self.subTest(offset=offset),self.assertRaises(RelationError):
                self.render(fixture(),offset)

    def test_folded_coverage_includes_owned_earlier_table_rows(self):
        values=fixture()
        values[2]['window_index']=0
        identity=(('native',0),('native',1))
        values[0]['windows'][0]=(identity,identity,identity,values[0]['windows'][1][3],values[0]['windows'][1][4])
        name,source=self.render(values,offset=0)
        self.assertEqual(name,'RuntimeOwnershipWindow000Program')
        coverage=source.split('theorem original_rows_covered',1)[1].split('theorem checked_bounds',1)[0]
        self.assertIn('row ∈ priorRows ++ (program lowBit highBit).rows',coverage)
        self.assertIn('row ∈ (priorRows ++ RuntimeOwnershipWindow000FoldedCompletion.rawRows)',coverage)
        self.assertIn('NativePrecompute.firstRows ++ RuntimeOwnershipWindow000Point1Cones.rawRows ++ RuntimeOwnershipWindow000Point1Completion.quotientRaw',source)
        self.assertIn('eval,Int.cast_one,one_mul',source)


if __name__=='__main__':
    unittest.main()
