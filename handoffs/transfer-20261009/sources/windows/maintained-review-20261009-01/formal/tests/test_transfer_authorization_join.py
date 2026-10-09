"""Typed caller-role refusal controls; synthetic fixtures are not runtime evidence."""
import copy
import json
import unittest

from circuits import transfer_authorization_join as join
from circuits import transfer_authorization_roles as roles
from circuits.transfer_balance_rows import canonical
from circuits.transfer_relation import RelationError


def fixture():
    """A synthetic source graph with the current component boundary LCs."""
    expressions = {}

    def witness(column):
        handle = (1, column - 3)
        expressions[handle] = ((column, 1),)
        return {'source': list(handle)}

    def node(index, terms):
        expressions[(2, index)] = canonical(terms)
        return {'source': [2, index]}

    def native(value):
        return {'native': f'{value:064x}'}

    caller = dict(regulated=witness(10), asset=witness(6), nk=witness(1993),
                  effective_nk=node(1, [(1993, 1), (61932, 1)]), registered_rnk=witness(1528),
                  ak=[witness(1980), witness(1981)],
                  address=[witness(c) for c in [1504, 1505, 1512, 1513]],
                  rnk_dh=[witness(1520), witness(1521)],
                  leaf_ring=[witness(23), witness(24)],
                  fixed_ring=[native(c) for c in join.FIXED_RING],
                  selected_ring=[node(2, [(0, join.FIXED_RING[0]), (33796, 1)]),
                                 node(3, [(0, join.FIXED_RING[1]), (33798, 1)])])
    spend = dict(ak=copy.deepcopy(caller['ak']), randomizer=witness(4000),
                 bits=[witness(c)['source'] for c in range(5000, 5252)],
                 generator=[native(0), native(1)],
                 contribution=[node(4, [(70000, 1)]), node(5, [(70001, 1)])],
                 computed=[node(6, [(70002, 1)]), node(7, [(70003, 1)])],
                 rk=[witness(70004), witness(70005)])
    bindings = dict(inputs=[witness(3763), witness(3764)] + caller['address'] +
                          [caller['asset']] + caller['selected_ring'],
                    hash=node(8, join.RNK_HASH), commitment=node(9, join.RNK_COMMITMENT),
                    regulated=caller['regulated'], registered=caller['registered_rnk'],
                    effective_nk=caller['effective_nk'])
    ivk = [caller['nk']['source'], *[v['source'] for v in caller['ak']],
           node(10, [(49500, 1)])['source']]
    encoded_expressions = [dict(source=list(h), terms=[[c, f'{v:064x}'] for c, v in terms])
                           for h, terms in sorted(expressions.items())]
    obj = dict(schema='shieldd-transfer-authorization-roles-v1', family='transfer', scope=roles.SCOPE,
               relation_digest='a' * 64, domain_size=262144, full_rows=200770, constant_copy=200692,
               ordinary_full_ordered_rows_equal=True, ivk_handles=ivk, caller=caller,
               spend=spend, rnk_bindings=bindings, expressions=encoded_expressions)
    shape = dict(relation_digest=obj['relation_digest'], domain_size=obj['domain_size'],
                 constant_copy=obj['constant_copy'])
    rnk = dict(shape, full_rows=obj['full_rows'], ivk_handles=ivk, base=caller['rnk_dh'],
               rnk_bindings=bindings, expressions=encoded_expressions)
    ivk_meta = dict(shape, stored_rows=obj['full_rows'], handles=ivk,
                    ordinary_full_ordered_rows_equal=True, expressions=encoded_expressions)
    checked = roles.inspect_metadata((json.dumps(obj) + '\n').encode(), obj['relation_digest'], ivk, rnk, ivk_meta)
    ring = dict(identity=dict(relation_digest=obj['relation_digest'], domain_size=obj['domain_size'],
                              stored_rows=obj['full_rows']),
                leaf_columns=[23, 24], fixed_coordinates=list(join.FIXED_RING))
    return checked, ring, [[(23, 1)], [(24, 1)]]


class AuthorizationJoinTests(unittest.TestCase):
    def test_typed_current_boundary_input(self):
        checked, ring, registry = fixture()
        state = join.inspect_join(checked, ring, registry)
        self.assertEqual(state['values']['asset'], ((6, 1),))

    def test_unchanged_handle_changed_role_lc_refused(self):
        for name in ['selected_ring', 'leaf_ring', 'effective_nk']:
            checked, ring, registry = fixture()
            reference = checked['metadata']['caller'][name]
            if isinstance(reference, list):
                reference = reference[0]
            handle = tuple(reference['source'])
            expression = next(e for e in checked['metadata']['expressions'] if tuple(e['source']) == handle)
            expression['terms'][0][1] = f'{2:064x}'
            # Even a changed parser output cannot bypass current role validation.
            checked['observed'][handle] = tuple((c, int(v, 16)) for c, v in expression['terms'])
            with self.subTest(name=name), self.assertRaisesRegex(RelationError, 'component LC mismatch|witness/column mismatch'):
                join.inspect_join(checked, ring, registry)

    def test_changed_captured_native_fixed_coordinate_refused(self):
        checked, ring, registry = fixture()
        checked['metadata']['caller']['fixed_ring'][0]['native'] = f'{1:064x}'
        with self.assertRaisesRegex(RelationError, 'component LC mismatch'):
            join.inspect_join(checked, ring, registry)

    def test_changed_hash_or_commitment_lc_refused(self):
        for role in ['hash', 'commitment']:
            checked, ring, registry = fixture()
            handle = tuple(checked['metadata']['rnk_bindings'][role]['source'])
            expression = next(e for e in checked['metadata']['expressions'] if tuple(e['source']) == handle)
            expression['terms'][0][1] = f'{1:064x}'
            checked['observed'][handle] = tuple((c, int(v, 16)) for c, v in expression['terms'])
            with self.subTest(role=role), self.assertRaisesRegex(RelationError, 'hash/commitment LC mismatch'):
                join.inspect_join(checked, ring, registry)

    def test_changed_accepted_ring_roles_refused(self):
        for key, value in [('leaf_columns', [24, 23]), ('leaf_columns', [23.0, 24]),
                           ('fixed_coordinates', [1, 2])]:
            checked, ring, registry = fixture()
            ring[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(RelationError):
                join.inspect_join(checked, ring, registry)

    def test_changed_accepted_registry_lc_refused(self):
        for registry in [[[(23, 2)], [(24, 1)]], [[(23, True)], [(24, 1)]],
                         [[(23.0, 1)], [(24, 1)]], [[(23, 1)], [(25, 1)]],
                         [[(23, 1), (99, 0)], [(24, 1)]], [[], [(24, 1)]]]:
            checked, ring, _ = fixture()
            with self.subTest(registry=registry), self.assertRaises(RelationError):
                join.inspect_join(checked, ring, registry)

    def test_changed_relation_shape_refused(self):
        for key, value in [('relation_digest', 'b' * 64), ('domain_size', 524288),
                           ('stored_rows', 200769), ('stored_rows', '200770')]:
            checked, ring, registry = fixture()
            ring['identity'][key] = value
            with self.subTest(key=key), self.assertRaises(RelationError):
                join.inspect_join(checked, ring, registry)

    def test_metadata_and_parser_lcs_must_agree(self):
        checked, ring, registry = fixture()
        checked['observed'][(2, 1)] = ((1993, 2), (61932, 1))
        with self.assertRaisesRegex(RelationError, 'parser expression mismatch'):
            join.inspect_join(checked, ring, registry)


if __name__ == '__main__':
    unittest.main()
