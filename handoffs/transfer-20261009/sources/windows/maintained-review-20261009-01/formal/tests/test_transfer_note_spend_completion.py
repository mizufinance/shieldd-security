"""Actual-LC completion plans: fused outputs, owned writes and strict refusals."""
import copy
import unittest
from circuits import transfer_note_spend as notes, generate_transfer_note_spend as complete
from circuits.transfer_relation import RelationError
from tests.test_transfer_note_spend import fixture


class NoteSpendCompletionTests(unittest.TestCase):
    def plan(self,**options):
        args=fixture(**options);extracted=notes.extract(*args)
        return args,extracted,complete.completion_plan(args[0],extracted,args[2])

    def test_actual_pivots_all_prior_source_roles_kept_and_thirteen_row_coverage(self):
        args,extracted,plan=self.plan()
        self.assertEqual(plan['writes'],[967,975,968,976,969,977])
        self.assertTrue({0,1,2,1000,8,503,513,966,964,961}.issubset(plan['kept']))
        for lc in args[2]['observed'].values():
            self.assertTrue(all(c in plan['kept'] for c,_ in lc))
        self.assertFalse(set(plan['writes'])&set(plan['kept']))
        text=complete.generate_completion(args[0],extracted,args[2])
        self.assertEqual(text.count('#print axioms'),11)
        self.assertIn('CompilerCompletion.original_rows_complete',text)
        self.assertIn('NoteSpendCompletion.source_equations',text)
        self.assertIn('theorem complete_two_spends',text)
        self.assertIn('set_option maxRecDepth 4096',text)
        self.assertIn('CompilerOrder.checked_order',text)
        self.assertNotIn('Topological kept [] completionSteps := by decide',text)
        self.assertIn('have dummyValue : eval rho dummy = optional.bit',text)
        self.assertIn('have leftAgree : eval (stage0 rho) left1',text)
        self.assertNotIn('(satisfied :',text)

    def test_fused_remainders_are_subtracted_and_swapped_products_supported(self):
        args,extracted,plan=self.plan(fused=True,swapped=True)
        self.assertEqual([p['remainder'] for p in plan['products']],[((8,3),),((8,4),),((8,5),)])
        self.assertTrue(all(p['swapped'] for p in plan['products']))
        text=complete.generate_completion(args[0],extracted,args[2])
        self.assertIn('def remainder0 : Linear := [(8, (3 : Int))]',text)
        self.assertIn('materialized_value',text)
        self.assertIn('def left0 : Linear := Compiler.subtract synthetic optionalRealNullifier',text)

    def test_nonunit_or_ambiguous_output_is_explicitly_refused(self):
        for options in ({'ambiguous':True},{'nonunit':True}):
            args=fixture(**options);extracted=notes.extract(*args)
            with self.subTest(options=options),self.assertRaisesRegex(RelationError,'pivot absent/ambiguous'):
                complete.generate_completion(args[0],extracted,args[2])

    def test_kept_prior_role_collision_is_refused(self):
        args,extracted,_=self.plan();accepted=copy.deepcopy(args[2])
        # A previously owned caller role outside the note capture is still kept.
        accepted['observed'][(2,9999)]=((967,1),)
        with self.assertRaisesRegex(RelationError,'pivot absent/ambiguous'):
            complete.generate_completion(args[0],extracted,accepted)


if __name__=='__main__':unittest.main()
