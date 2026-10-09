"""Synthetic Boolean algebra/row controls, without runtime/kernel credit."""
import copy
import unittest
from circuits import transfer_encryption_dh_boolean as boolean
from circuits.transfer_relation import MODULUS, RelationError


def fixture():
    # flagged = ((!is_fee & (regulated & external)) & !use_real).
    # is_fee itself is the asserted affine LC proof_context - 1.
    neg = MODULUS - 1
    derived = {(0, 0): ((0, 1),), (0, 1): ((0, neg),),
               (1, 0): ((3, 1),), (1, 1): ((4, 1),),
               (1, 2): ((5, 1),), (1, 3): ((6, 1),)}
    nodes = {}
    def add(index, multiply, left, right, lc):
        nodes[(2, index)] = (multiply, left, right)
        derived[(2, index)] = lc
        return (2, index)
    fee = add(0, False, (1, 0), (0, 1), ((0, neg), (3, 1)))
    minus_fee = add(1, True, (0, 1), fee, ((0, 1), (3, neg)))
    ordinary = add(2, False, (0, 0), minus_fee, ((0, 2), (3, neg)))
    eligible_reg = add(3, True, (1, 1), (1, 2), ((20, 1),))
    eligible = add(4, True, ordinary, eligible_reg, ((21, 1),))
    minus_real = add(5, True, (0, 1), (1, 3), ((6, neg),))
    unused = add(6, False, (0, 0), minus_real, ((0, 1), (6, neg)))
    flag = add(7, True, eligible, unused, ((22, 1),))
    return dict(bindings={'flagged': ('source', flag)}, nodes=nodes, derived=derived)


class EncryptionDhBooleanTests(unittest.TestCase):
    def test_real_row_matcher_requires_derived_flag_inputs_and_products(self):
        from unittest.mock import patch
        from tests.transfer_ownership_fixture import symbolic_window
        from circuits import transfer_encryption_dh as dh
        from circuits.transfer_balance_rows import canonical, combine
        checked, original = symbolic_window()
        checked = copy.deepcopy(checked)
        checked['points'].pop('target')
        checked['metadata'].update(schema='shieldd-transfer-encryption-dh-v1', role=0)
        checked['qualified'] = True
        small = fixture()
        # Disjoint source handles/columns, preserving the complete owned loop
        # fixture. Only the stream transport is mocked; row/formula matchers run.
        handle = lambda s: (s[0], s[1] + {0: 1000, 1: 8000, 2: 100000}[s[0]])
        lc = lambda terms: canonical((c + 8000 if c else 0, v) for c, v in terms)
        checked['derived'].update({handle(s): lc(terms) for s, terms in small['derived'].items()})
        checked['expressions'].update({handle(s): lc(terms) for s, terms in small['derived'].items()})
        checked['nodes'].update({handle(s): (m, handle(a), handle(b))
                                for s, (m, a, b) in small['nodes'].items()})
        checked['bindings'] = dict(flagged=('source', handle(small['bindings']['flagged'][1])),
                                   detection_key=checked['points']['base'], payload_key=checked['points']['base'])
        rows = copy.deepcopy(original['selected_rows'])
        obligations = []
        def emit(a, b, flag=False):
            index = max(row['row'] for row in rows) + 1
            encode = lambda terms: [[c, f'{v:064x}'] for c, v in
                                    canonical((16000 if c == 0 else c, v) for c, v in terms)]
            rows.append(dict(row=index, a=encode(a), b=encode(b)))
            if flag:
                obligations.append(index)
        for index in (248, 249):
            bit = checked['derived'][checked['bits'][index]]
            emit(bit, bit)
        plan = boolean.flag_plan(checked)
        for step in plan['steps']:
            if step['kind'] == 'assert':
                emit(step['terms'], step['terms'], True)
            elif step['kind'] == 'and':
                a, b = (checked['derived'][source] for source in step['inputs'])
                aux = ((9000 + len(rows), 1),)
                emit(combine(a, b, -1), aux, True)
                emit(combine(a, b), combine(aux, step['terms'], 4), True)
        def extract(candidate):
            checked['metadata']['full_rows'] = len(candidate)
            def replay(stream, expected_relation, row_observer):
                for row in candidate:
                    row_observer(row)
                return dict(relation_digest='a' * 64, domain_size=16384, stored_rows=len(candidate))
            with patch.object(dh.relation, 'inspect', side_effect=replay):
                return dh.extract_rows(checked, None, 'a' * 64)
        extracted = extract(rows)
        self.assertEqual(extracted['flag_boolean']['steps'][-1]['kind'], 'and')
        self.assertFalse(any('flagged.boolean' in item['roles'] for item in extracted['templates']))
        self.assertEqual(len(obligations), 10)
        for omitted in obligations:
            with self.subTest(omitted=omitted), self.assertRaises(RelationError):
                extract([row for row in rows if row['row'] != omitted])

    def test_nested_flag_uses_affine_assertion_and_input_rows(self):
        checked = fixture()
        plan = boolean.flag_plan(checked)
        self.assertEqual([step['kind'] for step in plan['steps']].count('not'), 2)
        asserted = [step for step in plan['steps'] if step['kind'] == 'assert']
        self.assertEqual(len(asserted), 4)
        self.assertIn(((0, MODULUS - 1), (3, 1)), [step['terms'] for step in asserted])
        self.assertNotIn('flagged.boolean', [step['obligation'] for step in asserted])
        extracted = dict(templates=[dict(roles=[step['obligation']], row=40 + i)
                                   for i, step in enumerate(asserted)],
                         products=[dict(role='node.' + str(i), rows=[50 + 2*i, 51 + 2*i])
                                   for i in (3, 4, 7)])
        attached = boolean.attach_rows(plan, extracted)
        self.assertEqual(attached['steps'][-1]['rows'], [64, 65])
        for role in ('input', 'product'):
            changed = copy.deepcopy(extracted)
            changed['templates' if role == 'input' else 'products'].pop()
            with self.subTest(role=role), self.assertRaises(RelationError):
                boolean.attach_rows(plan, changed)

    def test_wrong_complement_requires_its_own_boolean_row(self):
        checked = fixture()
        checked['derived'][(2, 6)] = ((0, 2), (6, MODULUS - 1))
        plan = boolean.flag_plan(checked)
        step = next(step for step in plan['steps'] if step['source'] == (2, 6))
        self.assertEqual(step['kind'], 'assert')

    def test_constants_square_and_folded_one_are_distinct(self):
        for value in (0, 1):
            plan = boolean.flag_plan(dict(bindings={'flagged': ('native', value)}))
            self.assertEqual(boolean.attach_rows(plan, dict(templates=[], products=[]))['steps'], [])
        with self.assertRaisesRegex(RelationError, 'not Boolean'):
            boolean.flag_plan(dict(bindings={'flagged': ('native', 2)}))
        checked = dict(bindings={'flagged': ('source', (2, 1))},
                       nodes={(2, 1): (True, (1, 0), (1, 0))},
                       derived={(1, 0): ((3, 1),), (2, 1): ((4, 1),)})
        plan = boolean.flag_plan(checked)
        extracted = dict(templates=[dict(roles=['flagged.input.1.0'], row=10),
                                   dict(roles=['node.1.square'], row=11)], products=[])
        self.assertEqual(boolean.attach_rows(plan, extracted)['steps'][-1]['rows'], [11])
        checked['derived'][(1, 0)] = ((0, 1),)
        checked['derived'][(1, 1)] = ((3, 1),)
        checked['derived'][(2, 1)] = ((3, 1),)
        checked['nodes'][(2, 1)] = (True, (1, 0), (1, 1))
        self.assertEqual(boolean.flag_plan(checked)['steps'][-1]['kind'], 'alias')
