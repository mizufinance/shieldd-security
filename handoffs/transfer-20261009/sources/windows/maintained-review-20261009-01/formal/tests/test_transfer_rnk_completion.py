import copy
import json
import unittest

from circuits.transfer_relation import MODULUS, RelationError
from circuits.transfer_balance_rows import canonical
from circuits import transfer_rnk_completion as completion


def row(index, a, b):
    encode = lambda terms: [[column, format(value, '064x')]
                            for column, value in canonical(terms)]
    return {'row': index, 'a': encode(a), 'b': encode(b)}


class RnkSparseCompletionTests(unittest.TestCase):
    def fixture(self):
        source = [row(10, [(1504, 1), (0, 1)], [(2257, 1)]),
                  row(11, [(2257, 1)], [(51214, 1)])]
        target = [row(20, [(1520, 1), (0, 1)], [(3013, 1)]),
                  row(21, [(3013, 1)], [(55995, 1)])]
        return source, target, [2257, 51214]

    def plan(self, fixture=None, protected=()):
        return completion.sparse_transport_plan(*(fixture or self.fixture()),
            domain_size=262144, full_rows=200770, protected_columns=protected)

    def test_restricted_map_accepts_global_alias_outside_scope(self):
        result = self.plan(protected=[1512, 1513, 3007, 3008])
        self.assertEqual(result['target_writes'], [3013, 55995])
        self.assertEqual(result['nonwritten_support'], [0, 1504])
        self.assertEqual(result['coverage'], [dict(target_row=20, source_rows=[10]),
                                             dict(target_row=21, source_rows=[11])])

    def test_json_roundtrip_preserves_certificate(self):
        fixture = json.loads(json.dumps(self.fixture()))
        self.assertEqual(self.plan(fixture), self.plan())

    def test_owned_image_collision_refused(self):
        source = [row(1, [(1504, 1)], [(1520, 1)])]
        target = [row(2, [(1520, 1)], [(1520, 1)])]
        with self.assertRaisesRegex(RelationError, 'write image collision'):
            self.plan((source, target, [1504, 1520]))

    def test_nonwritten_source_alias_refused(self):
        source = [row(1, [(1520, 1)], [(1504, 1)])]
        target = [row(2, [(1520, 1)], [(1520, 1)])]
        with self.assertRaisesRegex(RelationError, 'nonwritten support image alias'):
            self.plan((source, target, [1504]))

    def test_protected_target_refused(self):
        with self.assertRaisesRegex(RelationError, 'protected target'):
            self.plan(protected=[3013])

    def test_changed_actual_equation_refused(self):
        fixture = copy.deepcopy(self.fixture())
        fixture[1][1]['b'][0][1] = format(2, '064x')
        with self.assertRaisesRegex(RelationError, 'actual side coverage'):
            self.plan(fixture)

    def test_missing_source_or_extra_target_row_refused(self):
        fixture = copy.deepcopy(self.fixture());fixture[1].pop()
        with self.assertRaisesRegex(RelationError, 'missing transported source row'):
            self.plan(fixture)
        fixture = copy.deepcopy(self.fixture());fixture[1].append(row(22, [], []))
        with self.assertRaisesRegex(RelationError, 'actual side coverage'):
            self.plan(fixture)

    def test_typed_malformed_inputs_refused(self):
        for value in (True, -1, 262144):
            fixture = copy.deepcopy(self.fixture());fixture[2][0] = value
            with self.assertRaises(RelationError):self.plan(fixture)
        fixture = copy.deepcopy(self.fixture());fixture[0][0]['extra'] = 0
        with self.assertRaises(RelationError):self.plan(fixture)
        fixture = copy.deepcopy(self.fixture());fixture[0][0]['a'][0][1] = format(MODULUS, '064x')
        with self.assertRaises(RelationError):self.plan(fixture)

    def test_relation_shape_and_protected_collection_refused(self):
        for domain, count in ((0,1),(7,6),(8,9),(8,0),(True,1)):
            with self.assertRaises(RelationError):
                completion.sparse_transport_plan(*self.fixture(),domain_size=domain,full_rows=count)
        with self.assertRaises(RelationError):self.plan(protected=None)


class RnkSparseSequenceTests(unittest.TestCase):
    def block(self, source, target, writes):
        return dict(source_rows=source, target_rows=target, source_writes=writes)

    def plan(self, blocks, protected=()):
        return completion.sparse_sequence_plan(blocks, domain_size=262144,
            full_rows=200770, protected_columns=protected)

    def fixture(self):
        return [self.block([row(10, [(1504, 1)], [(2257, 1)])],
                           [row(20, [(1520, 1)], [(3013, 1)])], [2257]),
                self.block([row(11, [(2257, 1)], [(51214, 1)])],
                           [row(21, [(3013, 1)], [(55995, 1)])], [51214])]

    def test_one_source_cross_block_dependency_and_json_roundtrip(self):
        blocks = self.fixture()
        plan = self.plan(blocks, protected=[1512, 1513])
        self.assertEqual(plan['source_writes'], [2257, 51214])
        self.assertEqual(plan['nonwritten_support'], [1504])
        self.assertEqual(plan, self.plan(json.loads(json.dumps(blocks)), [1512, 1513]))

    def test_whole_write_collision_despite_each_local_plan(self):
        blocks = [self.block([row(1, [(1504, 1)], [])],
                             [row(2, [(1520, 1)], [])], [1504]),
                  self.block([row(3, [(1520, 1)], [])],
                             [row(4, [(1520, 1)], [])], [1520])]
        for block in blocks:
            completion.sparse_transport_plan(**block, domain_size=262144, full_rows=200770)
        with self.assertRaisesRegex(RelationError, 'whole write image collision'):
            self.plan(blocks)

    def test_whole_support_alias_despite_each_local_plan(self):
        blocks = [self.block([row(1, [(1504, 1)], [])],
                             [row(2, [(1520, 1)], [])], [1504]),
                  self.block([row(3, [(1520, 1)], [(51214, 1)])],
                             [row(4, [(1520, 1)], [(55995, 1)])], [51214])]
        for block in blocks:
            completion.sparse_transport_plan(**block, domain_size=262144, full_rows=200770)
        with self.assertRaisesRegex(RelationError, 'whole nonwritten support image alias'):
            self.plan(blocks)

    def test_duplicate_write_ownership_refused(self):
        blocks = self.fixture(); blocks.append(copy.deepcopy(blocks[0]))
        with self.assertRaisesRegex(RelationError, 'repeated physical write'):
            self.plan(blocks)

    def test_shared_row_identity_and_conflict(self):
        blocks = self.fixture()
        blocks[0]['source_rows'].append(row(12, [(0, 1)], []))
        blocks[0]['target_rows'].append(row(22, [(0, 1)], []))
        blocks[1]['source_rows'].append(row(12, [(0, 1)], []))
        blocks[1]['target_rows'].append(row(22, [(0, 1)], []))
        self.assertEqual(self.plan(blocks)['source_rows'], [10, 11, 12])
        blocks[1]['source_rows'][-1] = row(12, [(0, 2)], [])
        blocks[1]['target_rows'][-1] = row(22, [(0, 2)], [])
        with self.assertRaisesRegex(RelationError, 'conflicting shared physical row'):
            self.plan(blocks)

    def test_bound_and_typed_shape_and_protection(self):
        for blocks in ([], None, [{}], self.fixture() * 129):
            with self.assertRaises(RelationError):self.plan(blocks)
        blocks = self.fixture(); blocks[0]['extra'] = True
        with self.assertRaises(RelationError):self.plan(blocks)
        blocks = self.fixture()
        blocks[0]['source_rows'] = [row(i, [(2257, 1)], []) for i in range(513)]
        with self.assertRaisesRegex(RelationError, 'bounded nonempty row block'):
            self.plan(blocks)
        with self.assertRaisesRegex(RelationError, 'protected target'):
            self.plan(self.fixture(), [55995])


if __name__ == '__main__':
    unittest.main()
