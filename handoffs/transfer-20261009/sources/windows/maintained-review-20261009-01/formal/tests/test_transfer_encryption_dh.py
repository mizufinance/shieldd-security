"""Synthetic ingress controls; no runtime or circuit soundness evidence."""
import copy
import json
import unittest
from unittest.mock import patch
from circuits import transfer_encryption_dh as dh
from circuits.transfer_relation import RelationError


def encoded(value):
    return (json.dumps(value, separators=(',', ':')) + '\n').encode()


def native(value):
    return {'native': f'{value:064x}'}


def fixture(start=0, count=16, role=0, qualified=False):
    identity = [native(0), native(1)]
    bits = [[1, 100 + index] for index in range(252)]
    handles = bits + [[1, 500], [1, 501]]
    quotient = [native(0), native(1), native(1), native(1), *identity]
    return dict(schema='shieldd-transfer-encryption-dh-v1', family='transfer', scope=dh.SCOPE,
                relation_digest='a' * 64, domain_size=1024, full_rows=900, constant_copy=902,
                role=role, scalar={'source': [1, 500]}, flagged={'source': [1, 501]},
                detection_key=identity, payload_key=identity, base=identity, twice=identity,
                triple=identity, output=identity, bits=bits, window_start=start,
                window_count=count, total_windows=126,
                windows=[[identity] * 5 for _ in range(count)],
                window_bits=[bits[2 * (125 - start - offset):2 * (126 - start - offset)]
                             for offset in range(count)],
                quotients=[quotient] * (2 + 3 * count),
                expressions=[dict(source=handle, terms=[[3 + handle[1], f'{1:064x}']])
                             for handle in handles], nodes=[],
                ordinary_full_ordered_rows_equal=qualified, repeated_observations_equal=qualified)


class EncryptionDhIngressTests(unittest.TestCase):
    def test_all_five_occurrences_and_pending_qualification_are_distinct(self):
        for role in range(5):
            pending = fixture(role=role)
            accepted = dh.inspect_source_metadata(encoded(pending), 'a' * 64, role)
            self.assertFalse(accepted['qualified'])
            self.assertIn('proofs OPEN', accepted['scope'])
            with self.assertRaisesRegex(RelationError, 'qualification'):
                dh.inspect_qualified_metadata(encoded(pending), 'a' * 64, role)
            pending['ordinary_full_ordered_rows_equal'] = True
            pending['repeated_observations_equal'] = True
            self.assertTrue(dh.inspect_qualified_metadata(encoded(pending), 'a' * 64, role)['qualified'])

    def test_closed_shape_roles_and_flags(self):
        edits = {
            'role': lambda obj: obj.update(role=True),
            'foreign_role': lambda obj: obj.update(role=1),
            'extra': lambda obj: obj.update(target=[native(0), native(1)]),
            'identity': lambda obj: obj.update(relation_digest='b' * 64),
            'scalar': lambda obj: obj.update(scalar=native(1)),
            'repeat': lambda obj: obj.update(repeated_observations_equal=0),
            'ordinary': lambda obj: obj.update(ordinary_full_ordered_rows_equal=True),
            'detection': lambda obj: obj.update(detection_key=[native(1), native(1)]),
        }
        for name, edit in edits.items():
            obj = fixture()
            edit(obj)
            with self.subTest(name=name), self.assertRaises(RelationError):
                dh.inspect_source_metadata(encoded(obj), 'a' * 64, 0)

    def test_bit_point_and_quotient_associations(self):
        for edit in ('reverse', 'duplicate', 'window', 'quotient', 'endpoint', 'interval', 'native'):
            obj = copy.deepcopy(fixture(start=112, count=14))
            if edit == 'reverse': obj['window_bits'][0].reverse()
            elif edit == 'duplicate': obj['bits'][1] = obj['bits'][0]
            elif edit == 'window': obj['windows'][1][0] = [native(1), native(1)]
            elif edit == 'quotient': obj['quotients'][2][4] = native(1)
            elif edit == 'endpoint': obj['output'] = [native(1), native(1)]
            elif edit == 'interval': obj['window_count'] = 15
            else: obj['base'][0] = {'native': 'F' * 64}
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                dh.inspect_source_metadata(encoded(obj), 'a' * 64, 0)

    def test_rehashed_lc_changes_and_extra_graph_are_rejected(self):
        for edit in ('coefficient', 'constant_copy', 'extra', 'missing', 'topology'):
            obj = fixture()
            if edit == 'coefficient': obj['expressions'][0]['terms'][0][1] = f'{2:064x}'
            elif edit == 'constant_copy': obj['expressions'][0]['terms'][0][0] = 902
            elif edit == 'extra': obj['expressions'].append(dict(source=[1, 502], terms=[[505, f'{1:064x}']]))
            elif edit == 'missing': obj['expressions'].pop()
            else: obj['nodes'].append(dict(index=1, multiply=False, left=[2, 1], right=[1, 500]))
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                dh.inspect_source_metadata(encoded(obj), 'a' * 64, 0)

    def test_affine_node_must_match_observed_lc(self):
        obj = fixture()
        obj['flagged'] = {'source': [2, 1]}
        obj['nodes'] = [dict(index=1, multiply=False, left=[1, 501], right=[0, 0])]
        obj['expressions'].insert(0, dict(source=[0, 0], terms=[[0, f'{1:064x}']]))
        obj['expressions'].append(dict(source=[2, 1], terms=[[0, f'{1:064x}'], [504, f'{1:064x}']]))
        accepted = dh.inspect_source_metadata(encoded(obj), 'a' * 64, 0)
        self.assertEqual(accepted['derived'][(2, 1)], ((0, 1), (504, 1)))
        obj['expressions'][-1]['terms'][0][1] = f'{2:064x}'
        with self.assertRaisesRegex(RelationError, 'affine LC/source disagreement'):
            dh.inspect_source_metadata(encoded(obj), 'a' * 64, 0)

    def test_exact_full_chunk_cover_and_cross_occurrence_refusal(self):
        chunks = [dh.inspect_source_metadata(encoded(fixture(16 * i, min(16, 126 - 16 * i))), 'a' * 64, 0)
                  for i in range(8)]
        accepted = dh.inspect_chunks(chunks)
        self.assertEqual(accepted['windows'], 126)
        self.assertFalse(accepted['qualified'])
        for edit in ('missing', 'order', 'role', 'scalar', 'lc', 'graph', 'mode'):
            changed = copy.deepcopy(chunks)
            if edit == 'missing': changed.pop()
            elif edit == 'order': changed[1], changed[2] = changed[2], changed[1]
            elif edit == 'role': changed[1]['metadata']['role'] = 1
            elif edit == 'scalar': changed[1]['metadata']['scalar'] = {'source': [1, 501]}
            elif edit == 'lc': changed[1]['expressions'][(1, 500)] = ((503, 2),)
            elif edit == 'mode': changed[1]['qualified'] = True
            else:
                changed[0]['nodes'][(2, 100)] = (False, (1, 500), (1, 501))
                changed[1]['nodes'][(2, 100)] = (True, (1, 500), (1, 501))
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                dh.inspect_chunks(changed)

    def test_actual_quotient_assertion_and_boolean_row_obligations(self):
        from tests.transfer_ownership_fixture import symbolic_window
        checked, original = symbolic_window()
        checked = copy.deepcopy(checked)
        checked['points'].pop('target')
        checked['metadata']['schema'] = 'shieldd-transfer-encryption-dh-v1'
        checked['metadata']['role'] = 0
        checked['qualified'] = True
        checked['bindings'] = {'flagged': ('source', checked['bits'][248]),
                               'detection_key': checked['points']['base'], 'payload_key': checked['points']['base']}
        rows = copy.deepcopy(original['selected_rows'])
        for index in (248, 249):
            terms = [[checked['bits'][index][1] + 3, f'{1:064x}']]
            rows.append(dict(row=max(row['row'] for row in rows) + 1, a=terms, b=terms))

        def extract(candidate):
            # Synthetic source rows only. The real ordinary-stream checker is
            # tested separately; no digest-qualified capture is claimed here.
            checked['metadata']['full_rows'] = len(candidate)
            def replay(stream, expected_relation, row_observer):
                for row in candidate:
                    row_observer(row)
                return dict(relation_digest='a' * 64, domain_size=16384, stored_rows=len(candidate))
            with patch.object(dh.relation, 'inspect', side_effect=replay):
                return dh.extract_rows(checked, None, 'a' * 64)

        accepted = extract(rows)
        self.assertIn('proofs OPEN', accepted['scope'])
        self.assertTrue(any('flagged.boolean' in item['roles'] for item in accepted['templates']))
        self.assertFalse(any(role.startswith('target.') or role.startswith('nonidentity')
                             for item in accepted['templates'] for role in item['roles']))
        assertions = [pair['rows'][-1] for pair in accepted['products']
                      if pair['role'].startswith('quotient.') and len(pair['rows']) == 3]
        self.assertTrue(assertions)
        for omitted in assertions:
            with self.subTest(omitted=omitted), self.assertRaisesRegex(RelationError, 'materialized product/assertion'):
                extract([row for row in rows if row['row'] != omitted])
        with self.assertRaisesRegex(RelationError, 'actual template'):
            extract(rows[:-1])
        checked['qualified'] = False
        with self.assertRaisesRegex(RelationError, 'qualified occurrence'):
            extract(rows)

    def test_independently_typed_epk_scalar_and_bit_join(self):
        from circuits import transfer_epk_fixed as epk
        from tests.test_transfer_epk_all_fixed import all_fixture
        parent, raw, capsules, caller = all_fixture()
        # The historical synthetic fixture predates the actual authorization
        # caller ABI: that qualifier has no repeated-observations field.
        caller['metadata'].pop('repeated_observations_equal')
        caller['metadata'].update(schema='shieldd-transfer-authorization-roles-v1', family='transfer')
        accepted_epk = epk.inspect_all_pages(encoded(parent), raw, capsules, caller)
        for role in range(5):
            slot = 0 if role == 0 else role - 1
            first = accepted_epk['scopes'][2 + slot]['chunks'][0]['metadata']
            parsed = []
            for ordinal in range(8):
                obj = fixture(16 * ordinal, min(16, 126 - 16 * ordinal), role, True)
                obj.update({key: parent[key] for key in dh.IDENTITY})
                obj['scalar'] = first['randomizer']
                obj['bits'] = first['bits']
                obj['window_bits'] = [obj['bits'][2 * (125 - obj['window_start'] - offset):
                                                2 * (126 - obj['window_start'] - offset)]
                                      for offset in range(obj['window_count'])]
                handles = sorted({tuple(value) for value in obj['bits']} |
                                 {tuple(obj['scalar']['source']), (1, 501)})
                obj['expressions'] = [dict(source=list(handle), terms=[[3 + handle[1], f'{1:064x}']])
                                      for handle in handles]
                parsed.append(dh.inspect_qualified_metadata(encoded(obj), parent['relation_digest'], role))
            full = dh.inspect_chunks(parsed)
            joined = dh.join_epk(full, accepted_epk)
            self.assertEqual(joined['slot'], slot)
            self.assertEqual(joined['published'], first['published'])
            self.assertIn('meaning OPEN', joined['scope'])
            pending = copy.deepcopy(full)
            for chunk in pending['chunks']:
                chunk['qualified'] = False
                chunk['metadata']['ordinary_full_ordered_rows_equal'] = False
                chunk['metadata']['repeated_observations_equal'] = False
            with self.assertRaisesRegex(RelationError, 'pending chunks'):
                dh.join_epk(pending, accepted_epk)
            for edit in ('scalar', 'bits', 'slot', 'parent', 'lc', 'page_parent'):
                changed = copy.deepcopy(accepted_epk)
                page = changed['scopes'][2 + slot]['chunks'][0]
                if edit == 'scalar': page['metadata']['randomizer'] = {'source': [1, 999]}
                elif edit == 'bits': page['metadata']['bits'][0], page['metadata']['bits'][1] = page['metadata']['bits'][1], page['metadata']['bits'][0]
                elif edit == 'slot': changed['scopes'][2 + slot]['slot'] = (slot + 1) % 4
                elif edit == 'parent': changed['parent']['repeated_observations_equal'] = False
                elif edit == 'lc': changed['observed'][tuple(first['randomizer']['source'])] = ((999, 1),)
                else: page['qualification_parent_sha256'] = 'f' * 64
                with self.subTest(role=role, edit=edit), self.assertRaises(RelationError):
                    dh.join_epk(full, changed)

    def test_key_selection_source_operand_and_polarity_controls(self):
        from circuits import transfer_encryption_dh_selection as selection
        from circuits.transfer_relation import MODULUS
        witness = lambda index: ('source', (1, index))
        selected = lambda index: ('source', (2, index))
        nodes = {}
        for offset, yes, no in ((0, 1, 2), (4, 3, 4)):
            nodes[(2, offset)] = (True, (0, 0), (1, no))
            nodes[(2, offset + 1)] = (False, (1, yes), (2, offset))
            nodes[(2, offset + 2)] = (True, (1, 0), (2, offset + 1))
            nodes[(2, offset + 3)] = (False, (1, no), (2, offset + 2))
        checked = dict(metadata={'role': 1}, bindings=dict(flagged=witness(0),
                       detection_key=(witness(1), witness(3)), payload_key=(witness(2), witness(4))),
                       points={'base': (selected(3), selected(7))}, nodes=nodes,
                       expressions={(0, 0): ((0, MODULUS - 1),),
                                    **{(1, index): ((index + 3, 1),) for index in range(5)}})
        self.assertEqual(len(selection.match_selection(checked)['cones']), 2)
        for edit in ('keys', 'flag', 'polarity', 'base', 'operator', 'role'):
            changed = copy.deepcopy(checked)
            if edit == 'keys':
                changed['bindings']['detection_key'], changed['bindings']['payload_key'] = changed['bindings']['payload_key'], changed['bindings']['detection_key']
            elif edit == 'flag': changed['bindings']['flagged'] = witness(1)
            elif edit == 'polarity': changed['expressions'][(0, 0)] = ((0, 1),)
            elif edit == 'base': changed['points']['base'] = (selected(7), selected(3))
            elif edit == 'operator': changed['nodes'][(2, 2)] = (False, (1, 0), (2, 1))
            else: changed['metadata']['role'] = True
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                selection.match_selection(changed)

    def test_key_selection_needs_boolean_semantics(self):
        from circuits import transfer_encryption_dh_selection as selection, poseidon_graph
        inputs = [('source', (1, index)) for index in range(3)]
        graph, handles = selection.expected_selection(*inputs)
        self.assertEqual(handles, [(1, 0), (1, 1), (1, 2)])
        self.assertEqual(poseidon_graph.evaluate(graph, [0, 7, 11]), 11)
        self.assertEqual(poseidon_graph.evaluate(graph, [1, 7, 11]), 7)
        # Exact selector arithmetic on a non-Boolean flag is interpolation.
        # Source matching alone must not promote it to a branch claim.
        self.assertEqual(poseidon_graph.evaluate(graph, [2, 7, 11]), 3)
        self.assertNotIn(3, (7, 11))
        closed, roles = selection.expected_selection(('native', 1), ('native', 7), ('native', 11))
        self.assertEqual(roles, [])
        self.assertEqual(poseidon_graph.evaluate(closed, []), 7)

    def test_five_occurrence_shared_key_and_scope_join(self):
        from circuits import transfer_epk_fixed as epk
        from tests.test_transfer_epk_all_fixed import all_fixture
        parent, raw, capsules, caller = all_fixture()
        caller['metadata'].pop('repeated_observations_equal')
        caller['metadata'].update(schema='shieldd-transfer-authorization-roles-v1', family='transfer')
        accepted_epk = epk.inspect_all_pages(encoded(parent), raw, capsules, caller)
        occurrences = []
        for role in range(5):
            slot = 0 if role == 0 else role - 1
            epk_source = accepted_epk['scopes'][2 + slot]['chunks'][0]['metadata']
            chunks = []
            for ordinal in range(8):
                obj = fixture(16 * ordinal, min(16, 126 - 16 * ordinal), role, True)
                obj.update({key: parent[key] for key in dh.IDENTITY})
                obj.update(scalar=epk_source['randomizer'], bits=epk_source['bits'], flagged=native(1))
                obj['window_bits'] = [obj['bits'][2 * (125 - obj['window_start'] - offset):
                                                2 * (126 - obj['window_start'] - offset)]
                                      for offset in range(obj['window_count'])]
                handles = sorted({tuple(handle) for handle in obj['bits']} | {tuple(obj['scalar']['source'])})
                obj['expressions'] = [dict(source=list(handle), terms=[[3 + handle[1], f'{1:064x}']]) for handle in handles]
                chunks.append(dh.inspect_qualified_metadata(encoded(obj), parent['relation_digest'], role))
            occurrences.append(dh.inspect_chunks(chunks))
        joined = dh.inspect_occurrences(occurrences, accepted_epk)
        self.assertEqual(joined['windows'], 630)
        self.assertEqual([join['slot'] for join in joined['epk_joins']], [0, 0, 1, 2, 3])
        self.assertIn('proof OPEN', joined['scope'])
        for edit in ('missing', 'order', 'flag', 'key', 'node'):
            changed = copy.deepcopy(occurrences)
            if edit == 'missing': changed.pop()
            elif edit == 'order': changed[1], changed[2] = changed[2], changed[1]
            elif edit in ('flag', 'key'):
                for chunk in changed[2]['chunks']:
                    if edit == 'flag': chunk['metadata']['flagged'] = native(0)
                    else: chunk['metadata']['payload_key'] = [native(7), native(1)]
            else:
                for chunk in changed[0]['chunks']: chunk['nodes'][(2, 9999)] = (False, (1, 2000), (1, 2010))
                for chunk in changed[1]['chunks']: chunk['nodes'][(2, 9999)] = (True, (1, 2000), (1, 2010))
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                dh.inspect_occurrences(changed, accepted_epk)


if __name__ == '__main__':
    unittest.main()
