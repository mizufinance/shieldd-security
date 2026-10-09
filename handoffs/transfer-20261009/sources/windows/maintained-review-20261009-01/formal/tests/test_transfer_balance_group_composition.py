"""Tiny exact numeric frame/refusal tests; actual5/8 capture is UNRUN."""
import unittest
from circuits import generate_transfer_balance_group_composition as groups
from circuits import transfer_relation as relation


class BalanceGroupCompositionTests(unittest.TestCase):
    def test_two_cursors_and_early_publication_exceptions_preserve_support(self):
        support={0,1,2,6,10,20,23000,23100,200692}
        writes={19,21,24000,24002}
        frame=groups._fence(support,writes)
        self.assertEqual(frame['exceptions'],[19])
        covered=lambda column:column<frame['low'] or 22738<=column<frame['high'] or column==200692
        self.assertTrue(all(covered(column) and column not in frame['exceptions'] for column in support))
        self.assertTrue(all(not covered(column) or column in frame['exceptions'] for column in writes))
        self.assertFalse(support&writes)
        # A single fresh floor could not handle the two independent regions:
        # these obligations use the exact dual bounds and explicit old holes.
        self.assertLess(min(writes),max(support-{200692}))

    def test_alias_and_unbounded_exception_plan_refuse(self):
        with self.assertRaisesRegex(relation.RelationError,'earlier support'):
            groups._fence({0,2,6,19,23100,200692},{19,24000})
        with self.assertRaisesRegex(relation.RelationError,'bounded exact write exceptions'):
            groups._fence({0,2,6,1000,25000},set(range(100,165)))
        with self.assertRaisesRegex(relation.RelationError,'allocation regions'):
            groups._fence({0,2,200693},{21})

    def test_no_native_group_module_before_real_qualification_and_replay(self):
        with self.assertRaises(relation.RelationError):
            groups.generate(b'{}',[],b'{}',[],b'{}',b'{}',{}, {},[],[],{'ordinary_replays':1})


if __name__=='__main__':unittest.main()
