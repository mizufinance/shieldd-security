import hashlib
import unittest
from unittest.mock import patch
from integration import transfer_indexing_controls as controls

class TransferIndexingControlsTests(unittest.TestCase):
    def test_exact_composition_preserves_inherited_sources(self):
        fixture = b'// source-only fixture\n' + controls.ANCHOR + b'}\n'
        inherited = {'unchanged.rs': b'preserve exact bytes'}
        with patch.object(controls, 'HOST_SHA256', hashlib.sha256(fixture).hexdigest()):
            result = controls.compose(inherited, fixture)
        self.assertEqual(inherited, {'unchanged.rs': b'preserve exact bytes'})
        self.assertEqual(result['unchanged.rs'], inherited['unchanged.rs'])
        self.assertEqual(result[controls.HOST].count(controls.HOOK), 1)
        self.assertEqual(result[controls.CONTROL], controls.RESOURCE.read_bytes())

    def test_changed_host_or_repeated_control_refused(self):
        fixture = controls.ANCHOR + b'}\n'
        with self.assertRaisesRegex(ValueError, 'exact accepted pin'):
            controls.compose({}, fixture)
        with patch.object(controls, 'HOST_SHA256', hashlib.sha256(fixture).hexdigest()):
            result = controls.compose({}, fixture)
            with self.assertRaises(ValueError): controls.compose(result, fixture)
            with self.assertRaises(ValueError): controls.compose({controls.CONTROL:b'changed'}, fixture)

    def test_no_prover_fixture_and_expected_fault_scope_are_explicit(self):
        text = controls.RESOURCE.read_text()
        self.assertIn('NOT stateless-admitted transactions', text)
        self.assertIn('duplicate committed transaction', text)
        self.assertIn('HostExecutionPhase::InBlock', text)
        self.assertIn('catch_unwind', text)
        self.assertIn('no Transfer effects were constructed', text)
        self.assertNotIn('.prove(', text)
        self.assertIn('host.rollback().await?', text)
        self.assertIn('storage.latest_snapshot().block_transaction_count(1)', text)

    def test_readback_composition_preserves_inherited_bytes_and_refuses_mutation(self):
        fixture = b'// complete synthetic service test module\n'
        inherited = {'preserved.rs': b'unchanged'}
        with patch.object(controls, 'SERVICE_TESTS_SHA256', hashlib.sha256(fixture).hexdigest()):
            result = controls.compose_readback_controls(inherited, fixture)
            self.assertEqual(result['preserved.rs'], b'unchanged')
            self.assertEqual(result[controls.SERVICE_TESTS], fixture + controls.READBACK_HOOK)
            self.assertEqual(result[controls.READBACK_CONTROL], controls.READBACK_RESOURCE.read_bytes())
            with self.assertRaises(ValueError): controls.compose_readback_controls(result, fixture)
            with self.assertRaises(ValueError): controls.compose_readback_controls({}, fixture + b'changed')
        self.assertEqual(inherited, {'preserved.rs': b'unchanged'})

    def test_readback_control_observes_unavailable_not_false_absence(self):
        text = controls.READBACK_RESOURCE.read_text()
        self.assertIn('ErrorKind::Unavailable', text)
        self.assertIn('before.verify(&after.boundary).is_err()', text)
        self.assertIn('queries.publish_committed(durable)', text)
        self.assertIn('old published boundary must not return an absence proof', text)
        self.assertNotIn('.prove(', text)
