"""Small real source/row matching fixtures; actual five-page capture UNRUN."""
import copy,importlib.util,unittest
from pathlib import Path
from unittest.mock import patch

from circuits import generate_transfer_balance_variable_completion as balance
from circuits import generate_transfer_balance_variable_tables as tables
from circuits import transfer_relation as relation
from circuits import generate_transfer_ownership_point_materializations as material
from circuits import generate_transfer_ownership_double_completion as double
from circuits import generate_transfer_ownership_selector_completion as selector
from circuits import generate_transfer_ownership_window_curve_completion as curve
from circuits import generate_transfer_ownership_completion as mixed
from circuits import generate_transfer_ownership_native_seed as seed
from circuits import generate_transfer_ownership_precompute_native as precompute
from circuits import generate_transfer_ownership_folded_window_completion as folded
from circuits import generate_transfer_ownership_folded_window_curve as folded_curve
from tests.test_transfer_balance_variable_completion import accepted_fixture
from tests.transfer_ownership_fixture import symbolic_window
from tests.test_transfer_ownership_folded_window_completion import fixture as folded_fixture
from tests.test_transfer_ownership_folded_window_curve import fixture as folded_curve_fixture


class BalanceVariableRenderingTests(unittest.TestCase):
    def test_native_table_frame_uses_actual_precompute_quotient_outputs(self):
        # These are real symbolic source/row matches, never a runtime capture.
        checked,extracted=accepted_fixture()
        whole=balance.completion.window_plan(checked,extracted,0,True)
        cones=balance.completion.cone_certificates(checked,extracted,0,True)
        plan=dict(whole,point_groups=[group for group in whole['point_groups'] if group['index'] in (0,1)])
        d=double.render_point(checked,extracted,plan,cones,0,balance.PREFIX)
        a=double.render_point(checked,extracted,plan,cones,1,balance.PREFIX)
        n=seed.render_seed(checked,cones,d[0])
        original=precompute.render_precompute(checked,plan,cones,d[0],a[0],n[0])
        name,source=tables.augment(original,checked,plan,d[0],a[0],n[0])
        self.assertEqual(name,original[0])
        self.assertEqual(source.count('#print axioms'),5)
        self.assertEqual(source.count('set_option pp.all true in'),5)
        self.assertIn('have inputs := native_inputs',source)
        self.assertIn('have built := native_precompute_complete',source)
        self.assertIn('ShielddPointCoordinateSeed.seed_preserves',source)
        self.assertIn('GroupCircuitOrder.run_outside',source)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        for forbidden in ('(nativeCoordinates :','(endpoint :','(satisfied :'):
            self.assertNotIn(forbidden,source)
        # Matching singleton shape alone must not certify the wrong source
        # point as 3base; the exact two original quotient output pivots matter.
        damaged=copy.deepcopy(checked)
        damaged['points']['triple']=damaged['points']['twice']
        with self.assertRaisesRegex(relation.RelationError,'quotient output/source'):
            tables.augment(original,damaged,plan,d[0],a[0],n[0])
        bad_plan=copy.deepcopy(plan)
        bad_plan['point_groups'].reverse()
        with self.assertRaisesRegex(relation.RelationError,'double/add source order'):
            tables.augment(original,checked,bad_plan,d[0],a[0],n[0])

    def test_actual_local_formula_is_exported_from_constructed_rows(self):
        checked,extracted=accepted_fixture()
        name,source=balance.render_program(checked,extracted,0,compiler_origin=1000)
        self.assertEqual(name,'RuntimeBalanceVariableWindow001Program')
        self.assertIn('GroupVariableCircuitNative.LocalFormula',source)
        self.assertIn('CurveCompletion.actual_window_formula base one linked',source)
        self.assertEqual(source.count('#print axioms'),5)
        self.assertEqual(source.count('set_option pp.all true in'),5)
        self.assertNotIn('(endpoint :',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('(outputRole :',source)
        damaged=copy.deepcopy(extracted)
        plan=balance.completion.window_plan(checked,extracted,0,False)
        required=next(stage['rows'][-1] for stage in plan['stages'] if stage['kind']=='quotient')
        damaged['selected_rows']=[row for row in damaged['selected_rows'] if row['row']!=required]
        with self.assertRaises(relation.RelationError):
            balance.render_program(checked,damaged,0,compiler_origin=1000)

    def test_odd129_pairing_preserves_binary_magnitude_and_zero(self):
        # Independent integer oracle: the actual first high operand is false,
        # followed by the source pairs in reverse order. No field reduction or
        # fixture native endpoint is allowed to stand in for this identity.
        for n in (0,1,2,3,1<<128,(1<<129)-1,0x123456789abcdef):
            bits=[bool(n&(1<<index)) for index in range(129)]
            pairs=[(bits[index],bits[index+1] if index+1<len(bits) else False)
                   for index in range(0,len(bits),2)][::-1]
            self.assertEqual(len(pairs),65)
            self.assertFalse(pairs[0][1])
            acc=0
            for low,high in pairs:acc=4*acc+int(low)+2*int(high)
            self.assertEqual(acc,n)
        helper=Path('circuits/ShielddSecurity/GroupVariableCircuitNative.lean').read_text()
        self.assertIn('GroupNativeMultiply.pair_loop_value',helper)
        self.assertIn('GroupVariableCircuitCompletion',helper)
        self.assertEqual(helper.count('#print axioms'),4)
        self.assertEqual(helper.count('set_option pp.all true in'),4)
        self.assertNotRegex(helper,r'\b(sorry|admit|axiom|native_decide)\b')

    def test_page_wrapper_reaches_actual_local_rows_once(self):
        checked,extracted=accepted_fixture()
        windows=balance.generate_window(checked,extracted,0)
        # The fixture is a later physical window. A routing sentinel tests
        # shared precompute dispatch; the window bodies below use real rows.
        precompute=[('shared-precompute-routing-sentinel','')]
        with patch.object(balance.variable,'inspect_pages',return_value={'chunks':[checked]*5}), \
                patch.object(balance.batch,'page_selection',return_value=extracted), \
                patch.object(balance,'generate_precompute',return_value=precompute) as table:
            first=list(balance.generate_page(b'',[], 'a'*64,{},[],extracted,0))
            later=list(balance.generate_page(b'',[], 'a'*64,{},[],extracted,1))
        self.assertEqual(first,precompute+windows)
        self.assertEqual(later,windows)
        self.assertEqual(table.call_count,1)
        self.assertEqual(len({name for name,_ in first}),len(first))
        self.assertEqual(len(later),12)
        # The wrapper reaches the actual row checker; lost numerator evidence
        # cannot silently yield an empty page with apparently successful output.
        damaged=copy.deepcopy(extracted)
        plan=balance.completion.window_plan(checked,extracted,0,False)
        required=next(stage['rows'][-1] for stage in plan['stages'] if stage['kind']=='quotient')
        damaged['selected_rows']=[row for row in damaged['selected_rows'] if row['row']!=required]
        with patch.object(balance.variable,'inspect_pages',return_value={'chunks':[checked]*5}), \
                patch.object(balance.batch,'page_selection',return_value=damaged):
            with self.assertRaises(relation.RelationError):
                list(balance.generate_page(b'',[], 'a'*64,{},[],damaged,1))

    def test_strict129_local_constructors_derive_curve_denominators(self):
        checked,extracted=accepted_fixture()
        with patch.object(balance.completion.ownership,'match_formulas',side_effect=AssertionError('252 parser forbidden')):
            modules=balance.generate_window(checked,extracted,0)
        self.assertEqual(len(modules),12)
        self.assertEqual(len({name for name,_ in modules}),12)
        for name,source in modules:
            self.assertTrue(name.startswith('RuntimeBalanceVariableWindow001'))
            self.assertEqual(source.count('#print axioms'),source.count('set_option pp.all true in'))
            self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        _,whole=modules[-1]
        self.assertIn('actual_window_complete',whole)
        self.assertIn('GroupCircuitSequenceCompletion.preserves_rows',whole)
        self.assertIn('imaginarySquare',whole)
        self.assertNotIn('(legal :',whole)
        self.assertNotIn('(satisfied :',whole)
        self.assertNotIn('(outputRole :',whole)
        malformed=copy.deepcopy(checked);malformed['metadata']['bit_width']=252
        with self.assertRaisesRegex(relation.RelationError,'strict local source schema'):
            balance.generate_window(malformed,extracted,0)
        # Even a qualified row identity cannot replace an actual numerator row.
        damaged=copy.deepcopy(extracted)
        plan=balance.completion.window_plan(checked,extracted,0,False)
        needed=next(stage['rows'][-1] for stage in plan['stages'] if stage['kind']=='quotient')
        damaged['selected_rows']=[row for row in damaged['selected_rows'] if row['row']!=needed]
        with self.assertRaises(relation.RelationError):balance.generate_window(checked,damaged,0)

    def test_existing_ownership_default_sources_remain_exact(self):
        before=Path('.work/diagnostics/transfer-implementation-20261002/balance-variable-neutral-source-01/before')
        if not before.exists():self.skipTest('retained authored before-source unavailable')
        checked,extracted=symbolic_window()
        checked['metadata_sha256']='a'*64
        old={}
        for module in (material,double,selector,curve,mixed,seed,precompute):
            path=before/(module.__name__.split('.')[-1]+'.py')
            spec=importlib.util.spec_from_file_location('circuits._before_'+path.stem,path)
            loaded=importlib.util.module_from_spec(spec);spec.loader.exec_module(loaded);old[module]=loaded
        cases=[(material,(checked,extracted,0,True)),(double,(checked,extracted)),
            (selector,(checked,extracted,0)),(curve,(checked,extracted,0)),
            (mixed,(checked,extracted)),(seed,(checked,extracted)),(precompute,(checked,extracted))]
        for module,args in cases:
            with self.subTest(module=module.__name__):
                self.assertEqual(old[module].generate(*args),module.generate(*args))

    def test_both_existing_folded_renderer_default_bytes_remain_exact(self):
        before=Path('.work/diagnostics/transfer-implementation-20261002/balance-variable-neutral-source-01/before')
        if not before.exists():self.skipTest('retained authored before-source unavailable')
        old={}
        for module in (folded,folded_curve):
            path=before/(module.__name__.split('.')[-1]+'.py')
            spec=importlib.util.spec_from_file_location('circuits._before_'+path.stem,path)
            loaded=importlib.util.module_from_spec(spec);spec.loader.exec_module(loaded);old[module]=loaded
        checked,extracted,plan,base=folded_fixture()
        with patch.object(folded.completion,'window_plan',return_value=plan),patch.object(folded.local,'generate',return_value=base):
            self.assertEqual(old[folded].generate(checked,extracted),folded.generate(checked,extracted))
        checked,extracted,plan,cones=folded_curve_fixture()
        with patch.object(folded_curve.folded,'generate',return_value=('RuntimeOwnershipWindow000FoldedCompletion','')), \
                patch.object(folded_curve.completion,'window_plan',return_value=plan), \
                patch.object(folded_curve.completion.owner,'cone_certificates',return_value=cones):
            self.assertEqual(old[folded_curve].generate(checked,extracted),folded_curve.generate(checked,extracted))


if __name__=='__main__':unittest.main()
