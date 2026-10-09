"""Source and exact small polynomial fixtures; no runtime or kernel credit."""
import copy
import re
import unittest
from circuits import generate_transfer_balance_final_add_completion as generator
from circuits import transfer_balance_final_add as final, transfer_relation as relation
from tests.test_transfer_balance_final_add import fixture


def plan():
    roles, rows, identity = fixture()
    matcher = final.Matcher(roles)
    for row in rows:
        matcher.observe(row)
    return matcher.finish(identity)


class FinalAddRendererTests(unittest.TestCase):
    def test_entire_original_row_and_actual_write_footprint(self):
        accepted = plan()
        name, source = generator.render_plan(accepted)
        self.assertEqual(name, 'RuntimeTransferBalanceFinalAddCompletion')
        indices = re.search(r'def originalIndices : List Nat := (.+)', source)[1]
        self.assertEqual(indices, str([row['row'] for row in accepted['selected_rows']]))
        writes = re.search(r'def ownedWrites : List Nat := (.+)', source)[1]
        # Quotients are written before their original compiler product pivots;
        # the footprint must follow execution order rather than sorted columns.
        self.assertEqual(writes, str([50,51,52,53,54,55,56,57,58,59,160,60,61,161,62,63]))
        self.assertEqual(source.count('refine ⟨'), len(accepted['selected_rows']))
        self.assertIn('Compiler.unoutline 200692 actual.a', source)
        self.assertIn('List.not_mem_nil,or_false', source)
        self.assertIn('GroupCircuitSequenceCompletion.preserves_rows', source)

    def test_calculated_sign_and_curve_derived_quotients(self):
        source = generator.render_plan(plan())[1]
        theorem = source.split('theorem actual_rows_complete',1)[1].split(' := by',1)[0]
        self.assertNotIn('Satisfies base', theorem)
        self.assertNotIn('GroupCircuitCompletion.Legal', theorem)
        self.assertNotIn('denominator', theorem)
        self.assertNotIn('outputPoint base', theorem)
        self.assertIn('GroupSignedPoint.signed_on_curve', source)
        self.assertIn('GroupQuotientPairCompletion.add_complete', source)
        self.assertIn('Compiler.checked_product_sound', source)
        self.assertIn('(numerator_x base one) (denominator_x base one)', source)
        self.assertNotIn('sorry', source)
        self.assertNotIn('nativeEndpoint', source)
        self.assertNotIn('namespace P :=', source)

    def test_all_named_exports_full_signatures_finite_budgets(self):
        source = generator.render_plan(plan())[1]
        exports = re.findall(r'^#print axioms (\w+)$', source, re.M)
        self.assertEqual(len(exports), 20)
        self.assertEqual(len(exports), len(set(exports)))
        for name in exports:
            self.assertIn('set_option pp.all true in\n#check @'+name+'\n#print axioms '+name, source)
        self.assertIn('maxHeartbeats 500000', source)
        self.assertIn('maxRecDepth 4096', source)

    def test_altered_semantic_plan_and_missing_original_row_refuse(self):
        for key in ('signed','numerator','denominator','stages','writes','parents'):
            changed = copy.deepcopy(plan())
            changed[key] = []
            with self.subTest(key=key), self.assertRaises(relation.RelationError):
                generator.render_plan(changed)
        changed = plan()
        changed['selected_rows'].pop(3)
        with self.assertRaises(relation.RelationError):
            generator.render_plan(changed)

    def test_protected_asset_and_actual_output_lc_tampering_refuse(self):
        changed = plan()
        changed['protected'].remove(6)
        with self.assertRaises(relation.RelationError):
            generator.render_plan(changed)
        changed = plan()
        changed['roles']['output'] = (((162,1),),((163,1),))
        with self.assertRaises(relation.RelationError):
            generator.render_plan(changed)
        for name in ('X.Y', 'namespace P := Unsafe', '', 17):
            with self.assertRaises(relation.RelationError):
                generator.render_plan(plan(),namespace=name)

    def test_copy_link_and_product_auxiliary_alteration_refuse(self):
        changed = plan()
        changed['selected_rows'][-1]['a'][1][1] = f'{relation.MODULUS-2:064x}'
        with self.assertRaises(relation.RelationError):
            generator.render_plan(changed)
        changed = plan()
        changed['stages'][0]['auxiliary'] = 6
        with self.assertRaises(relation.RelationError):
            generator.render_plan(changed)

    def test_actual_joint_path_refuses_unqualified_parents_before_rendering(self):
        from unittest.mock import patch
        with patch.object(generator, 'render_plan', side_effect=AssertionError('unqualified renderer reached')):
            with self.assertRaises(relation.RelationError):
                generator.generate_from_joint(b'{}\n', [], b'{}\n', [], b'{}\n', b'{}\n',
                                              {}, {}, [], [], {'ordinary_replays': 1})

    def test_joint_marker_is_typed_and_cannot_replace_exact_source_views(self):
        from unittest.mock import patch
        accepted=plan()
        # A dispatch sentinel only; no qualifier/schema is invented or adopted.
        source=dict(roles=accepted['roles'],variable_raw_pages=['sentinel-v'],
                    blinding_raw_pages=['sentinel-h'],caller_raw_page='sentinel-c')
        joint=dict(ordinary_replays=1,identity=accepted['identity'],parents=source,final_add=accepted)
        args=(None,None,None,None,None,None,None,None,None,None)
        with patch.object(generator.final,'from_ingress',return_value=source):
            self.assertEqual(generator.generate_from_joint(*args,joint),generator.render_plan(accepted))
            for update in (dict(ordinary_replays=True),dict(parents={}),dict(identity={})): 
                with self.subTest(update=update),self.assertRaises(relation.RelationError):
                    generator.generate_from_joint(*args,dict(joint,**update))

