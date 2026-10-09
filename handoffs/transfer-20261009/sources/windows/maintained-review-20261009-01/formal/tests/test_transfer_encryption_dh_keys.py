"""Synthetic owned source selector controls; no actual key/caller credit."""
import copy
import unittest
from circuits import transfer_encryption_dh_keys as keys
from circuits.transfer_relation import MODULUS, RelationError


def fixture():
    nodes, expressions, derived = {}, {}, {}
    for index in range(5):
        expressions[(1, index)] = derived[(1, index)] = ((index + 3, 1),)
    for axis, fallback in enumerate((19, 23, 29, 31)):
        expressions[(0, 2 * axis)] = derived[(0, 2 * axis)] = ((0, fallback),)
        expressions[(0, 2 * axis + 1)] = derived[(0, 2 * axis + 1)] = ((0, MODULUS - fallback),)
        offset = 3 * axis
        nodes[(2, offset)] = (False, (0, 2 * axis + 1), (1, axis + 1))
        nodes[(2, offset + 1)] = (True, (1, 0), (2, offset))
        nodes[(2, offset + 2)] = (False, (0, 2 * axis), (2, offset + 1))
    witness = lambda index: ('source', (2, index))
    return dict(qualified=True, expressions=expressions, derived=derived, nodes=nodes,
                bindings=dict(detection_key=(witness(2), witness(5)), payload_key=(witness(8), witness(11))))


class EncryptionDhKeySourceTests(unittest.TestCase):
    def test_both_selectors_have_same_regulated_flag_and_distinct_leaf_roles(self):
        inferred = keys.infer_regulated_selectors(fixture())
        self.assertEqual(inferred['regulated_candidate'], ('source', (1, 0)))
        self.assertEqual(inferred['selectors']['detection_key']['leaf'], (('source', (1, 1)), ('source', (1, 2))))
        self.assertEqual(inferred['selectors']['payload_key']['fallback'], (('native', 29), ('native', 31)))
        self.assertIn('roles OPEN', inferred['scope'])

    def test_changed_polarity_coordinate_flag_and_pending_capture_are_refused(self):
        for change in ('polarity', 'axis_flag', 'key_flag', 'root', 'leaf', 'pending'):
            checked = fixture()
            if change == 'polarity': checked['derived'][(0, 1)] = ((0, 19),); checked['expressions'][(0, 1)] = ((0, 19),)
            elif change == 'axis_flag': checked['nodes'][(2, 4)] = (True, (1, 1), (2, 3))
            elif change == 'key_flag':
                checked['nodes'][(2, 7)] = (True, (1, 1), (2, 6))
                checked['nodes'][(2, 10)] = (True, (1, 1), (2, 9))
            elif change == 'root': checked['nodes'][(2, 2)] = (True, (0, 0), (2, 1))
            elif change == 'leaf': checked['nodes'][(2, 0)] = (False, (0, 1), (0, 0))
            else: checked['qualified'] = False
            with self.subTest(change=change), self.assertRaises(RelationError):
                keys.infer_regulated_selectors(checked)

    def test_lc_coincidence_does_not_replace_independent_source_match(self):
        checked = fixture()
        # The candidate's constant LC remains 19 but its source graph contains
        # a different constant: the independent matcher must refuse it.
        checked['expressions'][(0, 0)] = ((0, 20),)
        with self.assertRaisesRegex(RelationError, 'source mismatch'):
            keys.infer_regulated_selectors(checked)
