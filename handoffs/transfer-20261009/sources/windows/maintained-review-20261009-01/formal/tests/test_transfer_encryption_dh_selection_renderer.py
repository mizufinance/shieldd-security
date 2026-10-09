"""Synthetic physical-row selector controls; no actual capture/kernel credit."""
import unittest
from circuits import generate_transfer_encryption_dh_selection as renderer
from circuits.transfer_balance_rows import canonical, combine
from circuits.transfer_relation import MODULUS, RelationError
from tests.test_transfer_encryption_dh_keys import fixture as key_fixture


def fixture(role=1):
    checked = key_fixture()
    checked.update(metadata=dict(schema='shieldd-transfer-encryption-dh-v1', role=role,
                   relation_digest='b' * 64, domain_size=4096, full_rows=2048, constant_copy=3500),
                   metadata_sha256='a' * 64)
    checked['bindings']['flagged'] = ('source', (1, 5))
    checked['expressions'][(1, 5)] = checked['derived'][(1, 5)] = ((8, 1),)
    checked['expressions'][(0, 20)] = checked['derived'][(0, 20)] = ((0, MODULUS - 1),)
    outputs = []
    for axis in range(2):
        detection = checked['bindings']['detection_key'][axis][1]
        payload = checked['bindings']['payload_key'][axis][1]
        offset = 12 + 4 * axis
        checked['nodes'][(2, offset)] = (True, (0, 20), payload)
        checked['nodes'][(2, offset + 1)] = (False, detection, (2, offset))
        checked['nodes'][(2, offset + 2)] = (True, (1, 5), (2, offset + 1))
        checked['nodes'][(2, offset + 3)] = (False, payload, (2, offset + 2))
        outputs.append(('source', (2, offset + 3)))
    checked['points'] = {'base': tuple(outputs) if role else checked['bindings']['detection_key']}
    rows = [(10, canonical([(0, 1), (3500, -1)]), ())]
    for handle, (multiply, left, right) in sorted(checked['nodes'].items()):
        a, b = checked['derived'][left], checked['derived'][right]
        if not multiply:
            value = combine(a, b)
        elif left[0] == 0 or right[0] == 0:
            scalar, other = (a, b) if left[0] == 0 else (b, a)
            value = canonical((c, v * scalar[0][1]) for c, v in other)
        else:
            value = ((200 + handle[1], 1),)
            aux = ((500 + handle[1], 1),)
            rows.extend([(20 + 2 * handle[1], combine(a, b, -1), aux),
                         (21 + 2 * handle[1], combine(a, b), combine(aux, value, 4))])
        checked['derived'][handle] = value
    encode = lambda terms: [[c, f'{v:064x}'] for c, v in canonical(terms)]
    outline = lambda terms: canonical((3500 if c == 0 else c, v) for c, v in terms)
    extracted = dict(metadata_sha256='a' * 64,
                     identity=dict(relation_digest='b' * 64, domain_size=4096, stored_rows=2048),
                     selected_rows=[dict(row=i, a=encode(a if i == 10 else outline(a)),
                                         b=encode(b if i == 10 else outline(b))) for i, a, b in sorted(rows)])
    return checked, extracted


class EncryptionDhSelectionRendererTests(unittest.TestCase):
    def test_actual_outer_product_rows_determine_both_interpolations(self):
        checked, extracted = fixture()
        name, source = renderer.generate(checked, extracted)
        self.assertEqual(name, 'RuntimeTransferEncryptionDh1Selection')
        self.assertIn('Compiler.checked_product_sound', source)
        self.assertIn('Compiler.checked_add_sound', source)
        self.assertIn('Compiler.unoutline_rows_sound', source)
        self.assertIn('axis0_interpolation', source)
        self.assertIn('axis1_interpolation', source)
        signature = source.split('theorem axis0_interpolation', 1)[1].split(':= by', 1)[0]
        self.assertIn('satisfied : Satisfies rho rawRows', signature)
        self.assertIn('have actual := rows_satisfied rho satisfied', source)
        self.assertNotIn('boolean', signature)
        self.assertNotIn('OnCurve', signature)

    def test_nested_selectors_retain_one_regulated_operand_and_native_fallbacks(self):
        checked, extracted = fixture()
        modules = renderer.generate_regulated(checked, extracted)
        self.assertEqual([name for name, _ in modules],
                         ['RuntimeTransferEncryptionDetectionKeySelection', 'RuntimeTransferEncryptionPayloadKeySelection'])
        for _, text in modules:
            self.assertIn('def flag : Linear := [(3, (1 : Int))]', text)
            self.assertIn('Compiler.checked_product_sound', text)
            self.assertIn('#check @axis1_interpolation', text)

    def test_unconditional_role_zero_has_actual_detection_lc_conclusions(self):
        checked, extracted = fixture(0)
        _, text = renderer.generate(checked, extracted)
        self.assertIn('eval rho out0 = eval rho yesX := rfl', text)
        self.assertNotIn('private theorem a0n', text)

    def test_wrong_physical_rows_source_lcs_identity_or_qualification_fail(self):
        for change in ('row', 'missing', 'link', 'output', 'digest', 'metadata', 'pending'):
            checked, extracted = fixture()
            if change == 'row': extracted['selected_rows'][-1]['b'][-1][1] = f'{7:064x}'
            elif change == 'missing': extracted['selected_rows'].pop()
            elif change == 'link': extracted['selected_rows'][0]['a'][0][1] = f'{2:064x}'
            elif change == 'output': checked['derived'][(2, 19)] = ((999, 1),)
            elif change == 'digest': extracted['identity']['relation_digest'] = 'c' * 64
            elif change == 'metadata': extracted['metadata_sha256'] = 'c' * 64
            else: checked['qualified'] = False
            with self.subTest(change=change), self.assertRaises(RelationError):
                renderer.generate(checked, extracted)

    def test_reversed_original_squares_are_selected_without_new_physical_rows(self):
        checked, extracted = fixture()
        for row in extracted['selected_rows'][1:]:
            row['a'] = [[c, f'{(-int(v, 16)) % MODULUS:064x}'] for c, v in row['a']]
        _, text = renderer.generate(checked, extracted)
        self.assertIn('RowOrientationSoundness.checked_rows', text)
        self.assertIn('Compiler.checked_product_sound', text)
