"""Synthetic actual-row rendering boundary controls; no kernel/capture credit."""
import copy
import unittest
from circuits import generate_transfer_encryption_dh_boolean as renderer
from circuits.transfer_encryption_dh_boolean import flag_plan, attach_rows
from circuits.transfer_relation import RelationError


def fixture():
    checked = dict(metadata=dict(schema='shieldd-transfer-encryption-dh-v1', role=0,
                   relation_digest='a' * 64, domain_size=1024, full_rows=100, constant_copy=900),
                   qualified=True, bindings={'flagged': ('source', (2, 0))},
                   nodes={(2, 0): (True, (1, 0), (1, 1))},
                   derived={(1, 0): ((3, 1),), (1, 1): ((4, 1),), (2, 0): ((5, 1),)})
    from circuits.transfer_balance_rows import canonical
    encode = lambda terms: [[c, f'{v:064x}'] for c, v in canonical(terms)]
    rows = [(10, [(0, 1), (900, -1)], []), (11, [(3, 1)], [(3, 1)]),
            (12, [(4, 1)], [(4, 1)]), (13, [(3, 1), (4, -1)], [(6, 1)]),
            (14, [(3, 1), (4, 1)], [(5, 4), (6, 1)])]
    extracted = dict(identity=dict(relation_digest='a' * 64, domain_size=1024, stored_rows=100),
                     templates=[dict(roles=['flagged.input.1.0'], row=11),
                                dict(roles=['flagged.input.1.1'], row=12)],
                     products=[dict(role='node.0', rows=[13, 14])],
                     selected_rows=[dict(row=i, a=encode(a), b=encode(b)) for i, a, b in rows])
    extracted['flag_boolean'] = attach_rows(flag_plan(checked), extracted)
    return checked, extracted


class EncryptionDhBooleanRendererTests(unittest.TestCase):
    def test_flag_comes_from_original_rows_and_boolean_inputs(self):
        checked, extracted = fixture()
        name, text = renderer.generate(checked, extracted)
        self.assertEqual(name, 'RuntimeTransferEncryptionDh0Flag')
        self.assertIn('originalRows : List Nat := [10, 11, 12, 13, 14]', text)
        self.assertIn('EncryptionDhBoolean.conjunction', text)
        self.assertIn('Compiler.checked_product_sound', text)
        self.assertIn('Compiler.unoutline_rows_sound', text)
        self.assertIn('#check @flag_boolean', text)
        signature = text.split('theorem flag_boolean', 1)[1].split(':= by', 1)[0]
        self.assertNotIn('boolean :', signature)
        self.assertIn('satisfied : Satisfies rho rawRows', signature)

    def test_changed_row_constant_link_and_captured_identity_are_refused(self):
        for change in ('input', 'product', 'link', 'identity', 'plan', 'missing', 'qualified'):
            checked, extracted = fixture()
            if change == 'input': extracted['selected_rows'][1]['b'][0][1] = f'{2:064x}'
            elif change == 'product': extracted['selected_rows'][-1]['b'][0][1] = f'{3:064x}'
            elif change == 'link': extracted['selected_rows'][0]['a'][0][1] = f'{2:064x}'
            elif change == 'identity': extracted['identity']['relation_digest'] = 'b' * 64
            elif change == 'plan': extracted['flag_boolean']['steps'][-1]['rows'].reverse()
            elif change == 'missing': extracted['selected_rows'].pop()
            else: checked['qualified'] = False
            with self.subTest(change=change), self.assertRaises(RelationError):
                renderer.generate(checked, extracted)

    def test_reversed_squared_inputs_keep_same_arbitrary_row_argument(self):
        from circuits.transfer_relation import MODULUS
        checked, extracted = fixture()
        for row in extracted['selected_rows'][1:]:
            row['a'] = [[c, f'{(-int(v, 16)) % MODULUS:064x}'] for c, v in row['a']]
        _, text = renderer.generate(checked, extracted)
        self.assertIn('RowOrientationSoundness.checked_rows', text)
        self.assertIn('rows_checked', text)
