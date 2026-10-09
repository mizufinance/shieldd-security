"""Finite permutation/refusal checks and one genuine retained local pair."""
from pathlib import Path
import importlib.util,json,runpy,unittest,sys
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
R=Path('C:/src/shieldd-formal')

class BalanceVariableRenamingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ns=runpy.run_path(str(P/'inspect-balance-local-template-01.py'),run_name='source_fixture')
        spec=importlib.util.spec_from_file_location('circuits.transfer_balance_variable_renaming',R/'circuits/transfer_balance_variable_renaming.py')
        cls.module=importlib.util.module_from_spec(spec);spec.loader.exec_module(cls.module)
        sys.modules['circuits.transfer_balance_variable_renaming']=cls.module
        page=ns['page'];programs=[None]
        for index,plan in zip((1,2),ns['plans'],strict=True):
            programs.append(dict(index=index,page_ordinal=0,window_offset=index,plan=plan,writes=plan['writes'],rows=plan['local_rows'],
                before_frame=(min(c for c in plan['writes'] if c<22738),min(c for c in plan['writes'] if c>=22738)),
                after_frame=(max(c for c in plan['writes'] if c<22738)+1,max(c for c in plan['writes'] if c>=22738)+1),
                incoming=page['windows'][index][0],outgoing=page['windows'][index][4],bits=page['window_bits'][index]))
        cls.accepted=dict(programs=programs,checked=ns['checked'],selections=[ns['selection']],
            protected=sorted(set(ns['plans'][0]['protected'])&set(ns['plans'][1]['protected'])),
            parent_sha256=ns['checked']['parent_sha256'],raw_page_sha256=ns['checked']['raw_page_sha256'],identity=ns['extraction']['identity'])

    def test_genuine_rows_stages_overlap_and_inverse(self):
        result=self.module._pair(self.accepted,1,2)
        self.assertEqual(len(result['row_pairs']),45)
        self.assertEqual(result['row_pairs'][-1],(200769,200769))
        forward=dict(result['columns']);reverse=dict(result['inverse'])
        self.assertEqual(set(forward),set(forward.values()))
        self.assertTrue(all(reverse[forward[c]]==c for c in forward))
        self.assertTrue(all(forward[reverse[c]]==c for c in reverse))
        self.assertFalse(result['qualification'])
        for c in (0,1,2,6,9,22737,200692):self.assertEqual(forward[c],c)

    def test_stage_coefficient_row_and_protected_refusal(self):
        with self.assertRaisesRegex(self.module.relation.RelationError,'window0'):
            self.module._pair(self.accepted,0,2)
        for kind in ('coefficient','row','protected'):
            accepted=dict(self.accepted);programs=list(accepted['programs']);target=dict(programs[2]);programs[2]=target;accepted['programs']=programs
            plan=dict(target['plan']);target['plan']=plan
            if kind=='coefficient':
                stages=[dict(stage) for stage in plan['stages']];plan['stages']=stages
                terms=list(stages[0]['input']);c,v=terms[0];terms[0]=(c,v+1);stages[0]['input']=tuple(terms)
            elif kind=='row':target['rows']=target['rows'][:-1]
            else:accepted['protected']=accepted['protected']+[target['writes'][0]]
            with self.assertRaises(self.module.relation.RelationError):self.module._pair(accepted,1,2)

    def test_general_cycles_and_collision_refusal(self):
        columns=self.module._Columns({0})
        columns.add(10,11);columns.add(11,12)
        forward,reverse=map(dict,columns.permutation())
        self.assertEqual(forward,{0:0,10:11,11:12,12:10})
        self.assertEqual(reverse,{0:0,11:10,12:11,10:12})
        with self.assertRaisesRegex(self.module.relation.RelationError,'injection'):columns.add(13,12)
        with self.assertRaisesRegex(self.module.relation.RelationError,'protected'):columns.add(0,15)

    def test_symbolic_helper_has_paired_named_audits(self):
        source=(R/'circuits/ShielddSecurity/GroupCircuitRenaming.lean').read_text()
        names=('step_commutes','run_commutes','point_commutes','rows_complete','local_constructor','local_formula')
        self.assertEqual(source.count('set_option pp.all true in'),6)
        for name in names:
            self.assertIn('#check @'+name,source);self.assertIn('#print axioms '+name,source)
        self.assertIn('induction sources generalizing base',source)
        self.assertNotRegex(source,r'\b(sorry|admit|native_decide|axiom)\b')

    def test_generated_symbolic_transport_and_full_fallback(self):
        path=R/'circuits/generate_transfer_balance_variable_renaming.py'
        spec=importlib.util.spec_from_file_location('circuits.generate_transfer_balance_variable_renaming',path)
        renderer=importlib.util.module_from_spec(spec);spec.loader.exec_module(renderer)
        match=self.module._pair(self.accepted,1,2)
        name,body=renderer._source(self.accepted,self.accepted['programs'][2],match,self.accepted['protected'])
        self.assertEqual(name,'RuntimeBalanceVariableWindow002Program')
        self.assertEqual(body.count('set_option pp.all true in'),8)
        self.assertIn('GroupCircuitRenaming.local_constructor columns columns_injective',body)
        self.assertIn('GroupCircuitRenaming.local_formula columns columns_injective',body)
        self.assertIn('actualRows.all',body)
        self.assertIn('GroupCircuitSequenceCompletion.run_preserves',body)
        self.assertIn('sequence_protected',body)
        # The qualified constructor retains one zero equality for each
        # materialization's constant-link row; these steps write no columns.
        self.assertEqual(body.count('.compiler (.equal [] [])'),3)
        self.assertNotIn('native_point',body)
        self.assertNotRegex(body,r'\b(sorry|admit|native_decide|axiom)\b')
        self.assertIn('except matching.relation.RelationError',path.read_text())
        self.assertIn('local.render_program',path.read_text())
        self.assertIn('if item[\'index\']<2:',path.read_text())
        expression=renderer._permutation_expression([(0,0),(10,11),(11,12),(12,10)])
        self.assertEqual(expression,'(((Equiv.refl Nat).trans (Equiv.swap 10 11)).trans (Equiv.swap 10 12))')
