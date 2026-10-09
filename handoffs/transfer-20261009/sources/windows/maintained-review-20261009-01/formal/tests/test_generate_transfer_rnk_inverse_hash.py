"""Typed support and source-render fixtures; no actual rows or kernel credit."""
import copy
import re
import unittest
from unittest.mock import patch
from circuits import generate_transfer_rnk_inverse_hash as generator
from circuits.transfer_relation import RelationError


def row(index,column):
    return dict(row=index,a=[[column,f'{1:064x}']],b=[])


class RnkInverseHashTests(unittest.TestCase):
    def fixture(self):
        blocks=[[row(index,3009+index)] for index in range(134)]
        inverse=[row(index,column) for index,column in zip(
            (38038,38039,181725,200769),(3763,60776,60777,200692))]
        roles=[]
        for start in range(0,126,16):
            count=min(16,126-start)
            roles.extend(dict(kind='window',window=start+i,chunk=start) for i in range(count))
            roles.append(dict(kind='bits',chunk=start))
        return (dict(domain_size=262144,full_rows=200770,roles=roles,
            row_blocks=[dict(target_rows=rows) for rows in blocks]),
            dict(roles=dict(copy=200692),writes=[3765,60776,60777],rows=inverse))

    def test_support_keeps_hash_writes_disjoint_and_bounded(self):
        plan,inverse=self.fixture()
        self.assertEqual(generator.inspect_support([b['target_rows'] for b in plan['row_blocks']],
            inverse['rows']),[1]*134+[4])

    def test_overwritten_support_rejected_at_both_interval_endpoints(self):
        plan,inverse=self.fixture()
        for column in (60778,61929):
            with self.subTest(column=column):
                rows=[b['target_rows'] for b in copy.deepcopy(plan)['row_blocks']]
                rows[133][0]['a']=[[column,f'{1:064x}']]
                with self.assertRaises(RelationError):generator.inspect_support(rows,inverse['rows'])
        inverse['rows'][0]['a']=[[60778,f'{1:064x}']]
        with self.assertRaises(RelationError):generator.inspect_support(
            [b['target_rows'] for b in plan['row_blocks']],inverse['rows'])

    def test_typed_order_and_chunk_bound_refusals(self):
        plan,inverse=self.fixture();rows=[b['target_rows'] for b in plan['row_blocks']]
        for invalid in (None,rows[:-1],[None,*rows[1:]]):
            with self.assertRaises(RelationError):generator.inspect_support(invalid,inverse['rows'])
        with self.assertRaises(RelationError):generator.inspect_support(rows,inverse['rows'][:3])
        rows[0]=[row(index,3009) for index in range(513)]
        with self.assertRaises(RelationError):generator.inspect_support(rows,inverse['rows'])
        rows[0]=[row(1,3009),row(0,3010)]
        with self.assertRaises(RelationError):generator.inspect_support(rows,inverse['rows'])
        with self.assertRaises(RelationError):generator.generate(None,None,None)

    def test_exact_relation_and_inverse_write_refusals(self):
        plan,inverse=self.fixture()
        with patch.object(generator,'_validate',side_effect=lambda value:value), \
             patch.object(generator.inverse,'plan',return_value=inverse):
            for key,value in (('domain_size',131072),('full_rows',200769)):
                changed=copy.deepcopy(plan);changed[key]=value
                with self.assertRaises(RelationError):generator.generate({}, {},changed)
            inverse['writes']=[3765,60776,60778]
            with self.assertRaises(RelationError):generator.generate({}, {},plan)

    def test_finite_two_plus_eight_exports_use_one_assignment(self):
        plan,inverse=self.fixture()
        with patch.object(generator,'_validate',side_effect=lambda value:value) as validate, \
             patch.object(generator.inverse,'plan',return_value=inverse) as select:
            sources=generator.generate({}, {},plan)
        validate.assert_called_once_with(plan);select.assert_called_once_with({}, {},plan)
        self.assertEqual(set(sources),{'RuntimeRnkPreHashFootprint','RuntimeRnkInverseHashCompletion'})
        for name,count in (('RuntimeRnkPreHashFootprint',2),('RuntimeRnkInverseHashCompletion',8)):
            source=sources[name]
            checks=re.findall(r'^#check @([^\s]+)',source,re.M)
            self.assertEqual(len(checks),count)
            self.assertEqual(checks,re.findall(r'^#print axioms ([^\s]+)',source,re.M))
            self.assertNotRegex(source,r'\b(?:sorry|admit|native_decide|axiom)\b')
            self.assertNotRegex(source,r'\((?:satisfied|desired|priorTruth|hashTruth)\s*:')
        main=sources['RuntimeRnkInverseHashCompletion']
        self.assertIn('RuntimeRnkHashSequenceCompletion.completed (RuntimeRnkNativeInverseCompletion.completed',main)
        self.assertIn('original_inverse_complete',main)
        self.assertIn('hash_rows_complete',main)
        self.assertIn('10, 1512, 1513, 1520, 1521, 1528',main)
        self.assertNotIn('registered =',main)


if __name__=='__main__':unittest.main()
