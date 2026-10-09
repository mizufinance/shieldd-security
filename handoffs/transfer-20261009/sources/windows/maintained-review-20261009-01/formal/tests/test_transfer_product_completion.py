"""Local actual-row completion controls; no full-relation qualification."""
import copy
import io
import json
import unittest
from circuits import transfer_arithmetic as arithmetic, transfer_rk_addition as addition, transfer_relation as relation
from circuits.transfer_balance_rows import combine, canonical
from tests.test_transfer_rk_addition import fixture


class ProductCompletionTests(unittest.TestCase):
    def selection(self):
        data,accepted,ordinary=fixture()
        extracted=addition._extract_legacy(data,accepted,lambda:io.BytesIO(ordinary))
        obj,points,raw,normalized,values,operands,certificates,quotients=addition._selection(data,accepted,extracted)
        return data,accepted,extracted,raw,normalized,values,operands,certificates

    def test_exact_two_write_shape_emits_existing_symbolic_completion(self):
        data,accepted,extracted,raw,normalized,values,operands,certificates=self.selection()
        for name in ('xx','yy','sum','xy'):
            left,right=operands[name]
            c=arithmetic.product_completion_certificate(left,right,values[name],certificates[name],normalized)
            self.assertEqual(c['output'],values[name][0][0])
            self.assertEqual(c['rows'],certificates[name]['rows'])
            self.assertEqual(c['remainder'],())
        source=addition.generate(data,accepted,extracted)
        self.assertIn('CompilerCompletion.original_rows_complete',source)
        self.assertIn('CompilerCompletion.Topological, CompilerCompletion.Step.Shape',source)
        self.assertIn('List.not_mem_nil,or_false',source)
        for name in ('xx','yy','sum','xy'):
            for export in (name+'_product_ordered',name+'_product_coverage','complete_'+name):
                self.assertEqual(source.count('#check @'+export+'\n'),1)
        self.assertNotIn('(legal :',source[source.index('theorem complete_xx'):source.index('def xx_left')])

    def test_ambiguous_fused_unit_pivots_remain_unsupported(self):
        _,_,_,_,normalized,values,operands,certificates=self.selection()
        left,right=operands['xx'];c=certificates['xx'];output=combine(values['xx'],((999,1),))
        changed=copy.deepcopy(normalized)
        changed[c['rows'][1]]=(combine(left,right),combine(c['auxiliary'],output,4))
        matched=arithmetic.product_certificate(left,right,output,changed)
        self.assertIsNone(arithmetic.product_completion_certificate(left,right,output,matched,changed))

    def test_changed_original_row_and_input_pivot_alias_refuse_transport(self):
        _,_,_,_,normalized,values,operands,certificates=self.selection()
        left,right=operands['xx'];c=certificates['xx']
        changed=copy.deepcopy(normalized);changed[c['rows'][1]]=((),())
        self.assertIsNone(arithmetic.product_completion_certificate(left,right,values['xx'],c,changed))
        aliased=left
        changed[c['rows'][1]]=(combine(left,right),combine(c['auxiliary'],aliased,4))
        matched=arithmetic.product_certificate(left,right,aliased,changed)
        self.assertIsNone(arithmetic.product_completion_certificate(left,right,aliased,matched,changed))

    def test_swapped_actual_difference_is_kept_in_construction(self):
        _,_,_,_,normalized,values,operands,certificates=self.selection()
        left,right=operands['xx'];c=certificates['xx'];changed=copy.deepcopy(normalized)
        changed[c['rows'][0]]=(combine(right,left,-1),c['auxiliary'])
        matched=arithmetic.product_certificate(left,right,values['xx'],changed)
        completion=arithmetic.product_completion_certificate(left,right,values['xx'],matched,changed)
        self.assertEqual(completion['left'],right);self.assertEqual(completion['right'],left)

    def test_folded_and_square_shapes_are_not_product_constructions(self):
        for certificate in (dict(kind='square',rows=[0]),dict(kind='folded_left',rows=[])):
            self.assertIsNone(arithmetic.product_completion_certificate((),(),(),certificate,{}))

    def test_mixed_plan_covers_every_row_and_preserves_all_declared_roles(self):
        data,accepted,extracted,*_=self.selection()
        plan=addition.completion_plan(data,accepted,extracted)
        self.assertEqual([stage['kind'] for stage in plan['stages']],['product']*4+['quotient']*2)
        self.assertEqual(len(plan['writes']),14)
        self.assertEqual(len(plan['original_rows']),15)
        self.assertFalse(set(plan['writes']) & set(plan['kept']))
        self.assertEqual(json.loads(json.dumps(plan))['original_rows'],plan['original_rows'])
        source=addition.generate_completion(data,accepted,extracted)
        self.assertIn('GroupCircuitCompletion.original_rows_complete',source)
        self.assertIn('GroupCircuitOrder.checked_order kept [] completionSteps',source)
        self.assertNotIn('completionSteps := by decide',source)
        self.assertIn('List.not_mem_nil,or_false',source)
        self.assertIn('theorem actual_rows_complete',source)
        self.assertIn('(legalX : eval (productAssignment rho) denominator0 ≠ 0)',source)
        self.assertNotIn('(satisfied :',source)
        self.assertIn('theorem constructed_denominators',source)
        self.assertIn('Group.denominators_nonzero',source)
        self.assertIn('theorem actual_curve_rows_complete',source)
        self.assertEqual(source.count('#print axioms'),11)
        whole=addition.generate_whole_completion(data,accepted,extracted)
        self.assertEqual(whole.count('#print axioms'),13)
        self.assertIn('theorem actual_addition_complete',whole)
        self.assertIn('theorem actual_addition_group_complete',whole)
        self.assertIn('Group.affine_rows_onCurve',whole)
        self.assertNotIn('(satisfied :',whole)
        self.assertNotIn('(computedRole :',whole)

    def test_mixed_plan_refuses_alias_to_an_externally_owned_rk_role(self):
        def alias(rows):
            # Unit RK witness16 owns column19. A malformed compiler product
            # materializes xx there instead of its actual fresh pivot600.
            for row in rows:
                for side in ('a','b'):
                    row[side]=[[c,f'{v:064x}'] for c,v in canonical(
                        (19 if c==600 else c,int(v,16)) for c,v in row[side])]
        data,accepted,ordinary=fixture(alias)
        extracted=addition._extract_legacy(data,accepted,lambda:io.BytesIO(ordinary))
        with self.assertRaisesRegex(relation.RelationError,'writes alias kept/prior support'):
            addition.completion_plan(data,accepted,extracted)

    def test_mixed_plan_refuses_an_uncovered_real_fixture_row(self):
        data,accepted,ordinary=fixture(lambda rows:rows.append(dict(row=len(rows),a=[],b=[])))
        extracted=addition._extract_legacy(data,accepted,lambda:io.BytesIO(ordinary))
        extracted['selected_rows'].append(dict(row=15,a=[],b=[]))
        with self.assertRaisesRegex(relation.RelationError,'does not cover every selected original row'):
            addition.completion_plan(data,accepted,extracted)


if __name__=='__main__':unittest.main()
