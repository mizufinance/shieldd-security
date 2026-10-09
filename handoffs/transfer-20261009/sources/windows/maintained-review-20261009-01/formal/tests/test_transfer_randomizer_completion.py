"""Strict bit/comparator ownership recipes from typed ordinary-row fixtures."""
import copy
import io
import unittest
from circuits import transfer_fixed_spend as fixed, transfer_relation as relation, generate_transfer_fixed_spend as generate
from tests.fixed_spend_fixture import full_fixture


class RandomizerCompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.captures,cls.accepted,cls.ordinary=full_fixture()
        cls.extracted=fixed.extract_rows(cls.captures[0],cls.accepted,io.BytesIO(cls.ordinary),include_canonical=True)

    def test_exact_252_bit_block_and_all_251_product_pairs(self):
        plan=fixed.randomizer_completion_plan(self.captures[0],self.accepted,self.extracted)
        self.assertEqual(plan['width'],252)
        self.assertEqual(plan['value'],18)
        self.assertEqual(plan['bit_start'],103)
        self.assertEqual([stage['step'] for stage in plan['stages']],list(range(1,252)))
        self.assertEqual([stage for chunk in plan['chunks'] for stage in chunk],plan['stages'])
        self.assertTrue(all(len(chunk)<=16 for chunk in plan['chunks']))
        self.assertEqual(len(plan['writes']),754)
        self.assertEqual(len(plan['rows']),757)
        self.assertFalse(set(plan['writes'])&set(plan['kept']))
        self.assertTrue(set(range(103,355))<=set(plan['writes']))

    def test_omitted_canonical_rows_refuse_completion_recipe(self):
        extracted=fixed.extract_rows(self.captures[0],self.accepted,io.BytesIO(self.ordinary),include_canonical=False)
        with self.assertRaisesRegex(relation.RelationError,'needs canonical row extraction'):
            fixed.randomizer_completion_plan(self.captures[0],self.accepted,extracted)

    def test_bounded_order_generator_composes_all_251_exact_products(self):
        captures,accepted,ordinary=full_fixture(ordered_canonical=True)
        extracted=fixed.extract_rows(captures[0],accepted,io.BytesIO(ordinary),include_canonical=True)
        source=generate.generate_randomizer_order(captures[0],accepted,extracted)
        self.assertEqual(source.count('.product '),251)
        self.assertEqual(source.count('theorem checked_bound'),16)
        self.assertEqual(source.count('theorem checked_protected'),16)
        self.assertEqual(source.count('#print axioms'),3)
        self.assertIn('ScalarRandomizerCompletion.ordered_append',source)
        self.assertIn('ScalarRandomizerBounds.initial_rows_below',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('allStages := by decide',source)

    def test_bounded_order_refuses_nonmonotone_allocation(self):
        with self.assertRaisesRegex(relation.RelationError,'not bounded in captured order'):
            generate.generate_randomizer_order(self.captures[0],self.accepted,self.extracted)

    def test_constructive_generator_derives_endpoint_from_canonical_input(self):
        captures,accepted,ordinary=full_fixture(ordered_canonical=True)
        extracted=fixed.extract_rows(captures[0],accepted,io.BytesIO(ordinary),include_canonical=True)
        source=generate.generate_randomizer_completion(captures[0],accepted,extracted)
        self.assertEqual(source.count('theorem local_chain'),16)
        self.assertEqual(source.count('theorem local_bits'),16)
        self.assertEqual(source.count('#print axioms'),6)
        self.assertIn('ScalarRandomizerCompletion.constructs base 18 103 n',source)
        self.assertIn('(canonical : n < Scalar.order)',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('(ending :',source)
        self.assertNotIn('namespace O :=',source)
        self.assertNotIn('checkEndpoint',source)
        actual=generate.generate_randomizer_original_completion(captures[0],accepted,extracted)
        self.assertEqual(actual.count('theorem original_coverage'),16)
        self.assertEqual(actual.count('#print axioms'),7)
        self.assertIn('theorem actual_original_rows_complete',actual)
        self.assertIn('have endpointValue := completed.2.2.1',actual)
        self.assertNotIn('(satisfied :',actual)
        self.assertNotIn('(ending :',actual)
        reflected=generate.generate_randomizer_bit_completion(captures[0],accepted,extracted)
        self.assertEqual(reflected.count('#print axioms'),8)
        self.assertIn('theorem bit_reflection',reflected)
        self.assertIn('CompilerSupportPreservation.run_support',reflected)
        self.assertIn('(encodeBits 252 n)[index]?.getD false',reflected)
        self.assertNotIn('(satisfied :',reflected)

    def test_bit_write_alias_with_an_external_node_role_refuses(self):
        accepted=copy.deepcopy(self.accepted)
        handle=tuple(accepted['metadata']['rnk_bindings']['hash']['source'])
        accepted['observed'][handle]=((103,1),)
        for expression in accepted['metadata']['expressions']:
            if tuple(expression['source'])==handle:expression['terms']=[[103,f'{1:064x}']]
        # The receiving fixture declares an additional external consumer of
        # bit103. No new upstream runtime capture acceptance is claimed.
        with self.assertRaisesRegex(relation.RelationError,'bits alias an externally owned role'):
            fixed.randomizer_completion_plan(self.captures[0],accepted,self.extracted)


if __name__=='__main__':unittest.main()
