"""Ownership separation checks; these do not qualify a runtime observation."""
import copy
import unittest
from circuits import transfer_asset_map_full_completion as full,transfer_relation as relation


def ledger():
    return dict(join=dict(asset=((6,1),)),copy=200692,floor=189643,lower=20934,upper=21199,
        chunks=[dict(writes=[180000+20*i,180001+20*i]) for i in range(13)],
        map=dict(map=dict(recipe=dict(owned_writes=[20934,20935,20937,20938,21192,189643,190237])),
                 writes=[21198,190243,190244]))


class FullAssetOwnershipTests(unittest.TestCase):
    def test_two_native_cursors_and_all_thirteen_hash_pages_keep_actual_earlier_support(self):
        selected=ledger()
        full._check_later(selected)
        later=set(selected['map']['map']['recipe']['owned_writes'])|set(selected['map']['writes'])
        later.update(c for chunk in selected['chunks'] for c in chunk['writes'])
        before={c:17*c+3 for c in full.EARLIER_COLUMNS};after=dict(before)
        after.update({c:101*c+7 for c in later})
        self.assertEqual({c:after[c] for c in full.EARLIER_COLUMNS},before)
        self.assertEqual(len(selected['chunks']),13)

    def test_original_shared_product_inverse_and_copy_columns_refuse_later_writes(self):
        for column in full.EARLIER_COLUMNS:
            for group in ('hash','map','inverse'):
                damaged=ledger()
                if group=='hash':damaged['chunks'][-1]['writes'].append(column)
                elif group=='map':damaged['map']['map']['recipe']['owned_writes'].append(column)
                else:damaged['map']['writes'].append(column)
                with self.assertRaisesRegex(relation.RelationError,'later write overlaps'):
                    full._check_later(damaged)

    def test_exact_input_and_both_fences_are_required(self):
        for update in (dict(copy=32000),dict(join=dict(asset=((7,1),))),dict(lower=1000),dict(floor=40000)):
            damaged=ledger();damaged.update(copy.deepcopy(update))
            with self.assertRaises(relation.RelationError):full._check_later(damaged)


if __name__=='__main__':unittest.main()
