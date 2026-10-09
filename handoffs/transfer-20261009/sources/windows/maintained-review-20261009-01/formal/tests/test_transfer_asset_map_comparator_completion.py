"""Direct canonical255 written-bit semantics at integer boundaries."""
import io
import re
import unittest

from circuits import transfer_asset_map as maps, transfer_asset_map_comparator_completion as comparator
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture
from tests.test_asset_asserted_squares import defer_captured


class CanonicalComparatorConstructionTests(unittest.TestCase):
    def test_whole_constructor_derives_endpoint_and_transports_exact_row_partition(self):
        data, caller, stream, _, _ = fixture(17)
        extracted = maps.extract(data, stream, caller)
        recipe = comparator.plan(data, extracted, caller)
        name, source = comparator.generate(data, extracted, caller)
        self.assertEqual(name, 'RuntimeTransferAssetMapCanonicalConstruction')
        self.assertEqual(len(recipe['original_partition']), 766)
        self.assertEqual(set(recipe['original_partition']), set(recipe['raw']))
        self.assertEqual(len(recipe['original_partition']), len(set(recipe['original_partition'])))
        exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
        self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
        self.assertEqual(len(exports), 47)
        self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('ScalarConstructedBits.comparison_from_written_bits', source)
        self.assertIn('CompilerOrderComposition.append', source)
        self.assertIn('ScalarBitFootprint.initial_rows_below', source)
        self.assertIn('boundary_coverage_checked', source)
        self.assertIn('set_option maxRecDepth 4096', source)
        for theorem in ('endpoint_value', 'complete_rows'):
            statement = source[source.index('theorem '+theorem):]
            statement = statement[:statement.index(':= by')]
            self.assertNotIn('(satisfied', statement)
            self.assertNotIn('(endpoint', statement)
            self.assertNotIn('(capacity', statement)
        self.assertIn('(common_complete codec rho nativeValue)', source)
        self.assertIn('have endpointValue', source)
        self.assertEqual(source.count('have products'), 32)
        # Unit-step range inclusion is interval arithmetic. The more general
        # mem_range' introduces an existential index into the omega goal.
        self.assertEqual(source.count("simp only [List.mem_range'_1] at inside ⊢"), 32)
        self.assertEqual(source.count('exact List.mem_cons_self'), 1)
        self.assertNotIn('simp only [programChunks,List.mem_cons,List.mem_singleton]', source)
        self.assertIn('exact (List.mem_cons_of_mem _ List.mem_cons_self)', source)
        self.assertIn('⟨chain31,True.intro⟩', source)
        self.assertIn('⟨bits31,True.intro⟩', source)
        self.assertIn('Compiler.subtract endpoint [(0,1)]', source)
        self.assertIn('Compiler.eval_subtract', source)
        self.assertIn('simpa only [modulus,Scalar.modulus] using codec.bounded nativeValue', source)
        self.assertIn('[productOriginalChunks,List.mem_cons,List.not_mem_nil,or_false]', source)

    def test_generated_chunks_bind_actual_source_recurrence_and_owned_rows(self):
        data, caller, stream, _, _ = fixture(17)
        extracted = maps.extract(data, stream, caller)
        modules = comparator.generate_chunks(data, extracted, caller)
        self.assertEqual(len(modules), 32)
        self.assertEqual(sum(source.count('before :=') for source in modules.values()), 255)
        for source in modules.values():
            exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
            self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
            self.assertEqual(len(exports), 11)
            numeric = source[source.index('def steps :'):source.index('def sourceSteps :')]
            self.assertLessEqual(numeric.count('.product ['), 8)
            self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
            complete = source[source.index('theorem complete {'):source.index('#print axioms')]
            self.assertNotIn('(satisfied', complete[:complete.index(':= by')])
            self.assertNotIn('(endpoint', complete[:complete.index(':= by')])
            self.assertIn('ScalarRandomizerBounds.bounded_ordered', source)
            self.assertIn('source_chain_checked', source)
            self.assertIn('CompilerSignedCompletion.original_rows', source)
            self.assertIn('set_option maxRecDepth 2048', source)

    def test_native_canonical_boundary_and_shared_preservation(self):
        data, caller, stream, _, builder = fixture(17)
        for data, caller, raw, builder in (
                (data, caller, stream.getvalue(), builder),
                defer_captured(data, caller, stream.getvalue(), builder)):
            extracted = maps.extract(data, io.BytesIO(raw), caller)
            plan = comparator.plan(data, extracted, caller)
            self.assertEqual(len(plan['chunks']), 32)
            self.assertEqual(sum(len(c['comparisons']) for c in plan['chunks']), 255)
            self.assertTrue(all(len(c['steps']) <= 8 for c in plan['chunks']))
            self.assertEqual(len(plan['steps']), 254)
            self.assertGreater(2**255, maps.P)
            for value in (0, 1, maps.P - 1):
                base = dict(builder.rho)
                base.update({c: 17*c + 31 for c in plan['owned_writes']})
                base.update({1: 83, 2: 97, 32767: 113})
                result = comparator.construct(data, extracted, caller, base, value)
                rho = result['assignment']
                self.assertFalse(result['proof'])
                self.assertEqual(sum(rho[c]*2**i for i, c in enumerate(plan['bits'])), value)
                evaluate = lambda lc: sum(rho.get(c, 0)*n for c, n in lc) % maps.P
                self.assertEqual(evaluate(plan['checked']['canonical'][1]), 1)
                self.assertTrue(all(evaluate(a)**2 % maps.P == evaluate(b) for a, b in plan['raw'].values()))
                self.assertTrue(all(rho[c] == v for c, v in base.items() if c not in plan['owned_writes']))
                self.assertEqual([rho[c] for c in (0, 1, 2, 32000, 32767)], [1, 83, 97, 1, 113])
            for value in (-1, maps.P, 2**255 - 1, True):
                with self.assertRaisesRegex(relation.RelationError, 'canonical field integer'):
                    comparator.construct(data, extracted, caller, dict(builder.rho), value)


if __name__ == '__main__':
    unittest.main()
