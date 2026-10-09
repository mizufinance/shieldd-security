"""Independent decoded-view reference controls; these do not execute Rust."""
import copy
import unittest
import transfer_coverage as coverage


def body(context='ordinary'):
    return {'inputs': [11, 12], 'outputs': [
        {'note_commitment': 21, 'payload': b'complete-native-note-zero'},
        {'note_commitment': 22, 'payload': b'complete-native-note-one'}],
        'volume': {'day_start': 86400, 'nullifier': 31, 'commitment': 32,
                   'payload': b'complete-native-volume'}, 'context': context}


class TransferProjectionTests(unittest.TestCase):
    def test_projection_retains_all_slots_and_complete_payload_bytes(self):
        native = body()
        result = coverage.project_native_transfer(native, 'ordinary')
        self.assertEqual(result['nullifiers'], (11, 12))
        self.assertEqual(result['note_payloads'], (b'complete-native-note-zero', b'complete-native-note-one'))
        self.assertEqual(result['sct_commitments'], (21, 22, 32))
        self.assertEqual(result['volume_nullifiers'], ((86400, 31),))
        self.assertEqual(result['volume_payloads'], (b'complete-native-volume',))
        self.assertEqual(native, body())

    def test_same_public_commitments_do_not_replace_full_payload_projection(self):
        first = body()
        second = copy.deepcopy(first)
        second['outputs'][0]['payload'] = b'changed-native-note-ciphertext'
        a = coverage.project_native_transfer(first, 'ordinary')
        b = coverage.project_native_transfer(second, 'ordinary')
        self.assertEqual(a['public_effect_view'], b['public_effect_view'])
        self.assertNotEqual(a['note_payloads'], b['note_payloads'])
        second['volume']['payload'] = b'changed-volume-ciphertext'
        c = coverage.project_native_transfer(second, 'ordinary')
        self.assertEqual(a['public_effect_view'], c['public_effect_view'])
        self.assertNotEqual(a['volume_payloads'], c['volume_payloads'])

    def test_duplicate_occurrences_and_fee_slot_order_are_exact(self):
        ordinary = body()
        records = coverage.project_native_transfer_transaction([ordinary, ordinary], body('fee_funding'))
        self.assertEqual([record['slot'] for record in records], [('body', 0), ('body', 1), ('fee_funding',)])
        self.assertEqual([record['routing_index'] for record in records], [0, 1, 2])
        self.assertEqual(records[0]['effects'], records[1]['effects'])
        fee = records[2]['effects']
        self.assertEqual(fee['nullifiers'], (11, 12))
        self.assertEqual(fee['sct_commitments'], (21, 22))
        self.assertEqual(fee['volume_payloads'], ())
        self.assertEqual(fee['volume_nullifiers'], ())

    def test_context_shape_item_substitution_and_lossy_views_fail(self):
        for mutate in [lambda b: b['inputs'].pop(), lambda b: b['outputs'].reverse() or b['outputs'].pop(),
                       lambda b: b.update(context='fee_funding'),
                       lambda b: b['outputs'][0].update(payload=21),
                       lambda b: b['inputs'].__setitem__(0, True),
                       lambda b: b['volume'].update(day_start=-1),
                       lambda b: b.update(family='Transfer')]:
            native = body()
            mutate(native)
            with self.assertRaises(ValueError):
                coverage.project_native_transfer(native, 'ordinary')
        with self.assertRaises(ValueError):
            coverage.project_native_transfer({'family': 'Transfer', 'statement': 9, 'envelope': b'proof'}, 'ordinary')
        with self.assertRaisesRegex(ValueError, 'context mismatch'):
            coverage.project_native_transfer_transaction([body()], body())

    def test_reordering_is_visible_and_no_padding_classifier_filters_slots(self):
        native = body()
        native['inputs'] = [11, 11]
        native['outputs'][1]['note_commitment'] = 21
        reference = coverage.project_native_transfer(native, 'ordinary')
        self.assertEqual(reference['nullifiers'], (11, 11))
        self.assertEqual(reference['note_commitments'], (21, 21))
        native['outputs'].reverse()
        changed = coverage.project_native_transfer(native, 'ordinary')
        self.assertNotEqual(reference['note_payloads'], changed['note_payloads'])
        # Duplicate/freshness admission belongs to the execution model/runtime.
        self.assertEqual(reference['note_commitments'], changed['note_commitments'])


if __name__ == '__main__':
    unittest.main()
