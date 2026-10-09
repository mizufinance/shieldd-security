"""Bounded physical row coverage fixtures; no runtime/kernel qualification."""
import copy,unittest
from unittest.mock import patch
from circuits import transfer_ownership_constructor_join as join
from circuits.transfer_ownership_constructor_join import row_partition
from circuits.transfer_relation import RelationError


def row(index,column):
    return dict(row=index,a=[[column,f'{1:064x}']],b=[])


class ConstructorJoinTests(unittest.TestCase):
    def check(self,original,prior,local):
        return row_partition(original,prior,local,domain_size=128,full_rows=100)

    def test_once_only_precompute_plus_folded_rows_cover_originals(self):
        # Earlier two/three-base rows and local selector/output rows have
        # disjoint physical origins; their constant-copy row may be shared.
        precompute=[row(10,20),row(11,21),row(99,0)]
        folded=[row(12,22),row(13,23),row(99,0)]
        original=precompute[:2]+folded
        result=self.check(original,precompute,folded)
        self.assertEqual(result['prior_indices'],[10,11,99])
        self.assertEqual(result['local_indices'],[12,13,99])
        self.assertEqual(result['shared_indices'],[99])
        with self.assertRaisesRegex(RelationError,'missing earlier/local'):
            self.check(original,[],folded)

    def test_empty_original_and_parts_are_bounded_valid_coverage(self):
        self.assertEqual(self.check([],[],[])['original_indices'],[])
        self.assertEqual(self.check([row(12,22)],[],[row(12,22)])['prior_indices'],[])
        with self.assertRaises(RelationError):self.check([row(10,20)],[],[])

    def test_same_row_index_cannot_hide_changed_lc_or_orientation(self):
        actual=row(10,20)
        for mutation in ('column','coefficient','side'):
            changed=copy.deepcopy(actual)
            if mutation=='column':changed['a'][0][0]=21
            elif mutation=='coefficient':changed['a'][0][1]=f'{2:064x}'
            else:changed['a'],changed['b']=changed['b'],changed['a']
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):
                self.check([actual],[changed],[])
            with self.subTest(shared=mutation),self.assertRaises(RelationError):
                self.check([], [actual],[changed])

    def test_malformed_or_unbounded_rows_fail_closed(self):
        for rows in ([row(10,20),row(10,20)], [row(11,20),row(10,20)],
                     [dict(row=True,a=[],b=[])], [dict(row=100,a=[],b=[])],
                     [dict(row=10,a=[[128,f'{1:064x}']],b=[])], [dict(row=10,a=[],b=[],extra=0)]):
            with self.subTest(rows=rows),self.assertRaises(RelationError):self.check(rows,[],[])

    def test_actual_first_partition_requires_real_earlier_group_rows(self):
        checked=dict(metadata=dict(domain_size=128,full_rows=100))
        rows=[row(index,index) for index in (10,11,12,13,99)]
        extracted=dict(selected_rows=rows)
        local=dict(window_index=0,local_rows=[12,13,99])
        full=dict(point_groups=[dict(index=index,stage_start=index,stage_end=index+1)
                                for index in range(5)],
                  stages=[dict(rows=[index]) for index in (10,11,12,13,13)],constant_rows=[99])
        with patch.object(join.completion,'window_plan',side_effect=[local,full]), \
             patch.object(join.completion.owner,'cone_certificates',return_value=dict(rows={10:(),12:(),99:()})), \
             patch.object(join.completion.owner,'quotient_certificates',return_value=dict(rows={11:(),13:(),99:()})):
            result=join.actual_window_partition(checked,extracted,0)
        self.assertEqual(result['prior_indices'],[10,11,99])
        bad=copy.deepcopy(full);bad['stages'][0]['rows']=[]
        with patch.object(join.completion,'window_plan',side_effect=[local,bad]), \
             patch.object(join.completion.owner,'cone_certificates',return_value=dict(rows={10:(),12:(),99:()})), \
             patch.object(join.completion.owner,'quotient_certificates',return_value=dict(rows={11:(),13:(),99:()})), \
             self.assertRaisesRegex(RelationError,'missing earlier/local'):
            join.actual_window_partition(checked,extracted,0)


if __name__=='__main__':unittest.main()
