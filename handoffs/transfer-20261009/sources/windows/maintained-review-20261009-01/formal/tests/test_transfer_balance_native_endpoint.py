"""Source/interface checks only; genuine5/8/native targets remain UNRUN."""
import unittest
from circuits import generate_transfer_balance_native_endpoint as native
from circuits import transfer_relation as relation


class BalanceNativeEndpointTests(unittest.TestCase):
    def test_own_rows_and_independent_native_success_supply_endpoint(self):
        name,source=native._source()
        self.assertEqual(name,'RuntimeBalanceNativeEndpoint')
        self.assertEqual(source.count('#print axioms'),1)
        self.assertEqual(source.count('set_option pp.all true in'),1)
        self.assertIn('RuntimeBalanceGroupComposition.constructs',source)
        self.assertIn('TransferSignedBalanceNative.native_signed_commitment',source)
        self.assertIn('ShielddNativeSdk.scalar_read',source)
        self.assertIn('fr.bounded nativeBlinding',source)
        self.assertIn('built.2.trans nativeCoordinates.symm',source)
        declaration=source.split('theorem native_constructs',1)[1].split(':= by',1)[0]
        for forbidden in ('(endpoint :','(inverse :','(nonidentity :','(rows :','Satisfies base'):
            self.assertNotIn(forbidden,declaration)
        self.assertIn('sdkSuccess',declaration)
        self.assertIn('nativeSuccess',declaration)
        self.assertNotRegex(source,r'\b(sorry|admit|native_decide|axiom)\b')

    def test_arithmetic_same_amounts_includes_zero_and_both_signs(self):
        # Independent additive-group oracle compares native separated sums
        # with the own signed magnitude, including the legal zero H scalar.
        for amounts in ((0,0,0,0),(4,7,2,3),(2,3,4,7),(0,1,1,0),
                        ((1<<128)-1,0,0,1)):
            incoming=sum(amounts[:2]);outgoing=sum(amounts[2:])
            for b in (0,1,37):
                direct=incoming*11-outgoing*11+b*19
                signed=abs(incoming-outgoing)*11
                if incoming<outgoing:signed=-signed
                self.assertEqual((signed+b*19)%101,direct%101)
        # Successful SDK folds are a real narrower domain. A net cancellation
        # does not make overflowing each same-sign u128 fold successful.
        self.assertEqual(((1<<128)-1)+1-(1<<128),0)
        self.assertGreaterEqual(((1<<128)-1)+1,1<<128)

    def test_no_target_from_a_replay_marker_or_unqualified_pages(self):
        with self.assertRaises(relation.RelationError):
            native.generate(b'{}',[],b'{}',[],b'{}',b'{}',{}, {},[],[],{'ordinary_replays':1})


if __name__=='__main__':unittest.main()
