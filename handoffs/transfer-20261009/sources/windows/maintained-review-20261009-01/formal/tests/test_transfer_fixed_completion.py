"""Bounded actual-row ownership recipes from typed fixtures only."""
import io
import json
import unittest
from circuits import transfer_fixed_spend as fixed,transfer_relation as relation,generate_transfer_fixed_spend as generate
from tests.fixed_spend_fixture import full_fixture


class FixedCompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.captures,cls.accepted,cls.ordinary=full_fixture()
        cls.extracted=fixed.extract_rows(cls.captures[0],cls.accepted,io.BytesIO(cls.ordinary))

    def test_complete_bounded_stage_sequence_and_json_roundtrip(self):
        plan=fixed.fixed_completion_plan(self.captures[0],self.accepted,self.extracted)
        self.assertEqual([window['index'] for window in plan['windows']],list(range(16)))
        self.assertEqual(set(plan['original_rows']),{row['row'] for row in self.extracted['selected_rows']})
        self.assertFalse(set(plan['writes'])&set(plan['kept']))
        self.assertEqual(json.loads(json.dumps(plan))['writes'],plan['writes'])

    def test_unknown_extra_selected_row_is_not_covered(self):
        extracted=json.loads(json.dumps(self.extracted))
        known={row['row'] for row in extracted['selected_rows']}
        index=next(row['row'] for row in map(json.loads,self.ordinary.splitlines()[1:]) if row.get('row') not in known)
        extracted['selected_rows'].append(dict(row=index,a=[],b=[]))
        with self.assertRaisesRegex(relation.RelationError,'does not cover every selected original row'):
            fixed.fixed_completion_plan(self.captures[0],self.accepted,extracted)

    def test_generated_bounded_nonlinear_window_keeps_local_legality_explicit(self):
        source=generate.generate_window_completion(self.captures[0],self.accepted,self.extracted,1)
        self.assertIn('namespace ShielddSecurity.RuntimeFixedSpendWindow001Completion',source)
        self.assertIn('GroupCircuitCompletion.original_rows_complete',source)
        self.assertIn('theorem denominator_preserved',source)
        self.assertIn('(legalX : eval (productAssignment rho) denominator0 ≠ 0)',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('completionSteps := by decide',source)
        self.assertIn('GroupCircuitOrder.checked_order kept [] completionSteps (by decide)',source)
        ordered=source.split('theorem completion_ordered',1)[1].split('theorem ',1)[0]
        self.assertNotIn('simp [',ordered)
        self.assertEqual(source.count('#print axioms'),5)

    def test_curve_completion_derives_denominators_from_constructed_selector(self):
        source=generate.generate_window_curve_completion(self.captures[0],self.accepted,self.extracted,1)
        self.assertIn('theorem constructed_selector',source)
        self.assertIn('theorem constructed_denominators',source)
        self.assertIn('Group.denominators_nonzero',source)
        self.assertIn('Group.window_onCurve',source)
        self.assertIn('GroupCircuitCompletion.run_constructs',source)
        self.assertIn('(inputValid : Group.OnCurve',source)
        self.assertNotIn('(legalX :',source)
        self.assertNotIn('(legalY :',source)
        self.assertNotIn('(satisfied :',source)
        self.assertEqual(source.count('#print axioms'),8)

    def test_curve_completion_refuses_folded_first_window(self):
        with self.assertRaisesRegex(relation.RelationError,'six exact products and two quotients'):
            generate.generate_window_curve_completion(self.captures[0],self.accepted,self.extracted,0)

    def test_full_window_completion_derives_outgoing_curve_for_first_and_later(self):
        for offset,audits in ((0,2),(1,9)):
            source=generate.generate_window_complete(self.captures[0],self.accepted,self.extracted,offset)
            self.assertEqual(source.count('#print axioms'),audits)
            self.assertIn('theorem actual_window_complete',source)
            self.assertIn('have coverage :',source)
            self.assertIn('Group.affine_rows_onCurve',source)
            self.assertIn('arithmetic.1.1.trans (by unfold Group.cross; ring)',source)
            self.assertIn('xRow arithmetic.1.2',source)
            self.assertNotIn('(satisfied :',source)
            self.assertNotIn('(legalX :',source)
            self.assertNotIn('(legalY :',source)

    def test_global_join_requires_all126_and_retains_cross_chunk_supports(self):
        with self.assertRaisesRegex(relation.RelationError,'all126'):
            fixed.fixed_completion_join(self.captures[:1],self.accepted,[self.extracted])
        extractions=[self.extracted]+[fixed.extract_rows(capture,self.accepted,io.BytesIO(self.ordinary))
            for capture in self.captures[1:]]
        plan=fixed.fixed_completion_join(self.captures,self.accepted,extractions)
        self.assertEqual([program['index'] for program in plan['programs']],list(range(126)))
        self.assertEqual(set(plan['rows']),{row['row'] for extracted in extractions for row in extracted['selected_rows']})
        self.assertFalse(set(plan['kept'])&set(plan['writes']))
        earlier=set(column for program in plan['programs'][:16] for column in program['writes'])
        self.assertTrue(earlier<=set(plan['programs'][16]['prior_support']))
        for program in plan['programs']:
            self.assertFalse(set(program['writes'])&set(program['prior_support']))
        self.assertEqual(len(json.loads(json.dumps(plan))['programs']),126)

    def test_dual_cursor_bounds_preserve_initial_and_prior_rows(self):
        # A small symbolic allocation recipe, never a runtime observation.
        randomizer={'stages':[dict(output=100,auxiliary=101)]}
        raw={0:(((1,1),(100,1),(1000,-1)),()),
             1:(((10,1),(105,1),(1000,-1)),()),
             2:(((12,1),(109,1),(1000,-1)),())}
        def program(index,low,high,row):
            return dict(index=index,rows=[row],bit_support=[2],
                writes=[low,low+1,high,high+1,high+2,high+3],stages=[
                    dict(kind='product',output=high,auxiliary=high+1),
                    dict(kind='product',output=high+2,auxiliary=high+3),
                    dict(kind='linear',output=low),dict(kind='linear',output=low+1)])
        programs=[program(0,10,102,1),program(1,12,106,2)]
        bounds=fixed._completion_frames(programs,raw,[0],randomizer,1000)
        self.assertEqual(bounds['initial'],dict(low=10,high=102))
        self.assertEqual(bounds['frames'][0]['after'],bounds['frames'][1]['before'])
        self.assertEqual(bounds['frames'][1]['after'],dict(low=14,high=110))
        self.assertIn(1000,bounds['frames'][1]['support'])
        self.assertEqual(len(json.loads(json.dumps(bounds))['frames']),2)
        bad=json.loads(json.dumps(programs));bad[1]['stages'][0]['output']=105
        bad[1]['writes'][2]=105
        with self.assertRaisesRegex(relation.RelationError,'cursors are not contiguous'):
            fixed._completion_frames(bad,raw,[0],randomizer,1000)
        bad_raw=dict(raw);bad_raw[2]=(((900,1),),())
        with self.assertRaisesRegex(relation.RelationError,'local row support exceeds'):
            fixed._completion_frames(programs,bad_raw,[0],randomizer,1000)

    def test_typed_ordered_capture_bounds_and_program_adapter(self):
        captures,accepted,ordinary=full_fixture(ordered_fixed=True)
        extracted=fixed.extract_rows(captures[0],accepted,io.BytesIO(ordinary))
        bounds=fixed.fixed_completion_bounds(captures[0],accepted,extracted)
        self.assertEqual(bounds['initial'],dict(low=2000,high=8000))
        self.assertEqual(bounds['high_start'],6000)
        self.assertEqual(len(bounds['frames']),16)
        source=generate.generate_window_program(captures[0],accepted,extracted,1)
        self.assertEqual(source.count('#print axioms'),3)
        self.assertIn('actual_window_complete rho one',source)
        self.assertIn('GroupFixedCircuitBounds.checked_local',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('(legalX :',source)
        with self.assertRaisesRegex(relation.RelationError,'all126'):
            generate.generate_window_programs(captures[:1],accepted,[extracted])
        extractions=[extracted]+[fixed.extract_rows(capture,accepted,io.BytesIO(ordinary))
            for capture in captures[1:]]
        sources=generate.generate_window_programs(captures,accepted,extractions)
        self.assertEqual(len(sources),126)
        self.assertIn('RuntimeFixedSpendWindow125Program',sources)
        self.assertTrue(all(source.count('#print axioms')==3 for source in sources.values()))
        whole=generate.generate_full_completion(captures,accepted,extractions)
        self.assertEqual(whole.count('#print axioms'),3)
        self.assertIn('theorem actual_rows_complete',whole)
        self.assertIn('theorem actual_native_bytes_complete',whole)
        self.assertIn('GroupFixedCircuitCompletion.constructs',whole)
        self.assertIn('GroupFixedCircuitBounds.bounded_fresh',whole)
        self.assertNotIn('(satisfied :',whole)
        self.assertNotIn('(constructors :',whole)
        self.assertNotIn('(legalX :',whole)


if __name__=='__main__':unittest.main()
