import unittest
from circuits import generate_transfer_ownership_prefix_frame as generator
from circuits.transfer_relation import RelationError


class PrefixFrameTests(unittest.TestCase):
    def test_sparse_seed_exclusion_and_actual_frame_are_independent(self):
        rows=[(((1980,1),(51200,2),(200692,1)),())]
        name,source=generator._bounded('RuntimeOriginalBlock',rows,
            'RuntimeOwnershipWindow000PrecomputeFrame',200692,(2257,51233),{1504,1505,2253,51214})
        self.assertEqual(name,'RuntimeOriginalBlockOwnershipFrame')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertIn('CompilerWriteExclusion.checked_rows',source)
        self.assertIn('CompilerFrameCoverage.checked_rows',source)
        self.assertIn('def beforeFrame : GroupFixedCircuitBounds.Frame := ⟨2257,51233⟩',source)
        self.assertNotIn('Satisfies',source)

    def test_collision_or_uncovered_support_refuses(self):
        for column in (1504,1505,2253,51214,2257,22737,51233,200693):
            with self.subTest(column=column),self.assertRaises(RelationError):
                generator._bounded('RuntimeOriginalBlock',[(((column,1),),())],
                    'Frame',200692,(2257,51233),{1504,1505,2253,51214})
        with self.assertRaises(RelationError):
            generator._bounded('Block',[(((),()))]*129,'Frame',200692,(2257,51233),set())

    def test_all_owned_stage_write_forms(self):
        self.assertEqual(generator._stage_writes(dict(kind='square',output=1)),[1])
        self.assertEqual(generator._stage_writes(dict(kind='linear',output=2)),[2])
        self.assertEqual(generator._stage_writes(dict(kind='product',output=3,auxiliary=4)),[3,4])
        self.assertEqual(generator._stage_writes(dict(kind='quotient',quotient=5,product=6,auxiliary=7)),[5,6,7])
        with self.assertRaises(RelationError):generator._stage_writes(dict(kind='guessed'))

    def test_symbolic_original_block_composition(self):
        names=[f'RuntimeTransferIvkHashOwnedCompletionChunk{i}' for i in range(13)]
        names += [f'RuntimeTransferIvkComparison{phase}OriginalChunk{i}'
                  for phase,count in ((0,1),(1,16),(2,16)) for i in range(count)]
        names += ['RuntimeTransferIvkGateProductOriginal','RuntimeTransferIvkReductionTailCompletion',
                  'RuntimeTransferIvkInverseOwnedCompletion']
        name,source=generator._composition(names,'RuntimeOwnershipWindow000PrecomputeFrame',200692,(2257,51233))
        self.assertEqual(name,'RuntimeOwnershipIvkPrefixFrame')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertIn('CompilerWriteExclusion.flat_map_rows',source)
        self.assertIn('CompilerFrameCoverage.flat_map_rows',source)
        self.assertIn('List.not_mem_nil,or_false',source)
        self.assertNotIn('Satisfies',source)
        self.assertNotIn('native_decide',source)
        with self.assertRaises(RelationError):generator._composition(names[:-1],'Frame',200692,(2257,51233))


if __name__=='__main__':unittest.main()
