import copy
import unittest
from unittest.mock import patch

from circuits import generate_transfer_ownership_native_endpoint as generator
from circuits.transfer_relation import MODULUS, RelationError


def fixture():
    handles = [(1, 1509), (1, 1510), (1, 3004), (1, 3005)]
    last = dict(metadata=dict(relation_digest='a'*64, constant_copy=200692),
        points=dict(target=[('source', value) for value in handles[:2]],
                    output=[('source', value) for value in handles[2:]]),
        derived={value: ((column, 1),) for value, column in zip(handles, [1512,1513,3007,3008])})
    rows = [dict(row=index, a=[[target, f'{MODULUS-1:064x}'], [output, f'{1:064x}']], b=[])
        for index, target, output in [(180967,1512,3007),(180968,1513,3008)]]
    selected = dict(selected_rows=rows,
        templates=[dict(roles=['target.'+str(axis)], row=row['row']) for axis,row in enumerate(rows)])
    return [copy.deepcopy(last) for _ in range(8)], [dict(selected_rows=[],templates=[]) for _ in range(7)] + [selected]


class NativeEndpointTests(unittest.TestCase):
    def test_exact_source_handles_and_original_row_orientation(self):
        chunks, selected = fixture()
        with patch.object(generator.owner, 'join_chunks'):
            result = generator.endpoint_plan(chunks, selected)
        self.assertEqual(result['columns'], [1512,1513])
        self.assertEqual(result['output_columns'], [3007,3008])
        self.assertEqual(result['indices'], [180967,180968])

    def test_same_handle_with_changed_target_lc_refuses(self):
        chunks, selected = fixture()
        chunks[-1]['derived'][(1,1509)] = ((1514,1),)
        with patch.object(generator.owner, 'join_chunks'), self.assertRaises(RelationError):
            generator.endpoint_plan(chunks, selected)

    def test_orientation_is_not_a_hash_identity_substitute(self):
        chunks, selected = fixture()
        selected[-1]['selected_rows'][0]['a'] = [[1512,f'{1:064x}'],[3007,f'{MODULUS-1:064x}']]
        with patch.object(generator.owner, 'join_chunks'), self.assertRaises(RelationError):
            generator.endpoint_plan(chunks, selected)

    def test_conflicting_source_role_row_refuses(self):
        chunks, selected = fixture()
        selected[0]['templates'].append(dict(roles=['target.0'],row=180966))
        with patch.object(generator.owner, 'join_chunks'), self.assertRaises(RelationError):
            generator.endpoint_plan(chunks, selected)

    def test_missing_actual_row_fails_closed(self):
        chunks, selected = fixture()
        selected[-1]['selected_rows'].pop()
        with patch.object(generator.owner, 'join_chunks'), self.assertRaises(RelationError):
            generator.endpoint_plan(chunks, selected)

    def test_owned_seed_precedes_construction_and_endpoint_is_derived(self):
        chunks, selected = fixture()
        reduction = generator.scalar.native.bit_values.bits.consumer.keys.native.reduction
        ivk = generator.scalar.native.bit_values.bits.consumer.keys.native.hashes.ivk
        plan = dict(phases=[dict(value=((1994,1),),start=1996,width=4),
                            dict(value=((1995,1),),start=2000,width=252)])
        with patch.object(generator.owner,'join_chunks'), \
             patch.object(generator.scalar,'generate'), patch.object(generator.prefix,'generate'), \
             patch.object(ivk,'inspect_metadata',return_value={}), patch.object(reduction,'plan',return_value=plan):
            name, source = generator.generate(chunks, selected, b'ivk',{},b'reduction',{},'params','a'*64)
        self.assertEqual(name,'RuntimeOwnershipNativeEndpoint')
        self.assertEqual(source.count('#check @'),8)
        self.assertEqual(source.count('#print axioms'),8)
        self.assertIn('upstream.multiply (upstream.promote sender) scalar',source)
        self.assertIn('ScalarReductionFrame.column',source)
        self.assertIn('RuntimeOwnershipNativePrefix.prefix_and_windows_complete',source)
        self.assertIn('RuntimeOwnershipNativeScalar.native_scalar_coordinates',source)
        self.assertIn('RuntimeOwnershipWindow000PrecomputeFrame.outside',source)
        self.assertIn('ShielddNativeOwnershipMultiply.multiply_coordinates',source)
        self.assertNotIn('target_role',source)
        statement=source.split('theorem endpoint_rows_complete',1)[1].split(' := by',1)[0]
        self.assertEqual(statement.count('Satisfies'),1)
        self.assertNotIn('constructed',statement)
        self.assertNotIn('scalarMeaning',statement)


if __name__ == '__main__':
    unittest.main()
