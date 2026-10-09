import unittest
from circuits.generate_transfer_reduction import split_remainder


class ReductionSplittingTests(unittest.TestCase):
    def source(self):
        records=['import ShielddSecurity.TransferReduction','set_option maxHeartbeats 500000',
                 'set_option maxRecDepth 2048','namespace ShielddSecurity.RuntimeTransferRemainder',
                 'open Compiler','def copyColumn : Nat := 10',
                 'theorem block_included : True := by trivial']
        records += [f'theorem c{i}{suffix} : True := by trivial' for i in range(16)
                    for suffix in ('chain','bits','endpoint','included','chain_global','bits_global')]
        records += ['theorem checked_chain : True := by trivial','end ShielddSecurity.RuntimeTransferRemainder']
        return '\n\n'.join(records)+'\n'

    def test_every_chunk_and_membership_audit_retained(self):
        modules=split_remainder(self.source())
        self.assertEqual(len(modules),18)
        data=modules['RuntimeTransferRemainderData']
        self.assertIn('#check @block_included',data)
        self.assertIn('#print axioms block_included',data)
        for i in range(16):
            self.assertEqual(modules[f'RuntimeTransferRemainderChunk{i}'].count('#check @'),6)

    def test_missing_or_duplicate_theorem_fails_closed(self):
        for source in (self.source().replace('theorem c2bits : True := by trivial',''),
                       self.source().replace('theorem c2bits :','theorem c2chain :')):
            with self.assertRaises(ValueError): split_remainder(source)

    def test_prefix_must_be_module_identifier(self):
        with self.assertRaises(ValueError): split_remainder(self.source(),'bad;module')


if __name__=='__main__': unittest.main()
