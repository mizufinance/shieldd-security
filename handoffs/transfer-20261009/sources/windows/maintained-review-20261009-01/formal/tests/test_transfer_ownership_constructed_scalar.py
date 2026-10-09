import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_constructed_scalar as generator
from circuits.transfer_relation import RelationError


class ConstructedScalarTests(unittest.TestCase):
    def test_endpoint_uses_eight_bounded_traces_and_written_bits_without_target_rows(self):
        chunks=[dict(bits=[0],derived={0:((2000,1),)}) for _ in range(8)]
        with patch.object(generator.candidates,'validate_all_chunks'), \
             patch.object(generator.trace,'generate'), \
             patch.object(generator.owner,'generate_trace_composition'), \
             patch.object(generator.arithmetic,'generate'):
            name,source=generator.generate(chunks,[{}]*8)
        self.assertEqual(name,'RuntimeOwnershipConstructedScalar')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertIn('RuntimeOwnershipConstructedTraceTail000.actual_trace',source)
        self.assertIn('TransferOwnership.trace_scalar_coordinates',source)
        self.assertIn('ScalarConstructedBits.decoded_singletons',source)
        self.assertIn('ScalarWrittenBitValues.field_bit_value',source)
        self.assertIn('List.mem_range\'.mp',source)
        self.assertIn('encodeBits_value 252 n bounded',source)
        self.assertNotIn('endpointRows',source)
        self.assertNotIn('target_role',source)
        self.assertNotIn('.actual_ownership',source)
        self.assertIn('RuntimeOwnershipWindow125.result rho = model.coordinates (n • senderBase)',source)

    def test_requires_real_all126_source_join(self):
        with patch.object(generator.candidates,'validate_all_chunks',side_effect=RelationError('missing126 sources')):
            with self.assertRaises(RelationError):generator.generate([],[])

    def test_chunk_equations_are_opaque_and_boundary_transport_is_symbolic(self):
        modules=generator._render_modules(2000)
        self.assertEqual(len(modules),9)
        facts=modules['RuntimeOwnershipConstructedTraceFacts']
        self.assertIn('import ShielddSecurity.RuntimeOwnershipConstructorTrace\n',facts)
        self.assertIn("theorem actual_columns : RuntimeTransferOwnership.columns = List.range' 2000 252 := by rfl",facts)
        self.assertEqual(facts.count('theorem chunk_equations'),8)
        self.assertEqual(facts.count('theorem boundary'),7)
        self.assertEqual(facts.count('#check @'),16)
        self.assertEqual(facts.count('.actual_trace\n'),8)
        for offset in range(7):
            source=modules[f'RuntimeOwnershipConstructedTraceTail{offset:03d}']
            self.assertEqual(source.count('theorem actual_trace'),1)
            self.assertEqual(source.count('#check @'),1)
            self.assertEqual(source.count('Eq.mpr (congrArg'),1)
            self.assertEqual(source.count('exact (TransferOwnership.trace_equations_append (RuntimeTransferOwnership.coefficientD : F)'),1)
            self.assertNotIn('trace_equations_append _',source)
            self.assertNotIn('apply (TransferOwnership.trace_equations_append',source)
            self.assertNotIn('simpa only',source)
            self.assertNotIn('by decide',source)
            if offset<6:self.assertIn(f'import ShielddSecurity.RuntimeOwnershipConstructedTraceTail{offset+1:03d}',source)
        _,source=generator._render(2000)
        self.assertEqual(source.count('#check @'),2)
        self.assertNotIn('private theorem tail_equations',source)
        self.assertLess(source.index('import ShielddSecurity.RuntimeOwnershipConstructedTraceTail000'),source.index('set_option maxHeartbeats'))

    def test_pure_template_refuses_malformed_or_out_of_domain_columns(self):
        for start in (True,-1,0,262144-251,None,'2000'):
            with self.subTest(start=start):
                with self.assertRaises(RelationError):generator._render(start)


if __name__=='__main__':unittest.main()
