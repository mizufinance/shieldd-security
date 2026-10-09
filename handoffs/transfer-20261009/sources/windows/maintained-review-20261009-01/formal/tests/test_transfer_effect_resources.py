"""Offline checks of fresh-stage test resources, never runtime proof controls."""
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class TransferEffectResourcesTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((ROOT / 'state/transfer_effect_controls.json').read_text())
        self.source = (ROOT / self.manifest['resource']).read_text()
        self.patch = (ROOT / self.manifest['patch']).read_text()

    def test_resource_identity_and_unqualified_scope(self):
        m = self.manifest
        self.assertEqual(m['runtime_commit'], json.loads((ROOT / 'shieldd.lock').read_text())['sha'])
        self.assertEqual(m['status'], 'source_only_not_runtime_tested')
        self.assertEqual(m['evidence'], [])
        for key in ['resource', 'patch']:
            self.assertEqual(hashlib.sha256((ROOT / m[key]).read_bytes()).hexdigest(), m[key + '_sha256'])
        self.assertNotIn(b'\r\n', (ROOT / m['patch']).read_bytes(),
                         'the exact pinned Rust blobs require LF patch context')
        self.assertEqual(len(m['base_files']), 3)
        self.assertEqual(len(m['patched_text_sha256']), 4)
        self.assertEqual(len(m['tests']), 6)

    def test_test_only_faults_follow_production_effects(self):
        transaction = self.patch.split('--- a/crates/core/app/src/action_handler/transaction.rs')[1].split('--- a/crates/core/app/src/app/delivery.rs')[0]
        delivery = self.patch.split('--- a/crates/core/app/src/app/delivery.rs')[1].split('--- /dev/null')[0]
        resource = self.patch.split('--- /dev/null')[1]
        self.assertLess(transaction.index('stage_action_routing'), transaction.index('fv.Transfer.after_routing'))
        self.assertLess(delivery.index('fv.Transfer.after_index'), delivery.index('let events = state_tx.apply().1'))
        for section, fault in [(transaction, 1), (delivery, 2)]:
            self.assertIn('+', section)
            self.assertIn('#[cfg(test)]', section)
            self.assertIn('Some((tx_id.0, ' + str(fault) + '))', section)
        # This new child module is exactly the reviewed formal-owned resource.
        added = '\n'.join(line[1:] for line in resource.splitlines()
                          if line.startswith('+') and not line.startswith('+++')) + '\n'
        self.assertEqual(added, self.source)

    def test_genuine_full_transfer_builders_and_error_causes(self):
        self.assertIn('family_fixtures().await?', self.source)
        self.assertIn('setup_test_txs(2).await?', self.source)
        self.assertIn('deliver_tx_bytes', self.source)
        self.assertNotIn('without_proof', self.source)
        self.assertNotIn('Verified::', self.source)
        self.assertIn('contains("daily volume nullifier")', self.source)
        self.assertIn('contains(expected)', self.source)
        self.assertIn('assert!(!app.state.is_nullifier_spent(nullifier)', self.source)
        self.assertIn('volume_nullifier_exists(volume.day_start, volume.nullifier)', self.source)

    def test_exact_slots_volume_order_and_late_rollback_observations(self):
        for marker in ['transfer.body.inputs.len(), 2', 'transfer.body.outputs.len(), 2',
                       'pending_nullifiers()', 'pending_note_payloads()',
                       'pending_volume_accumulator_payloads()', 'canonical_fee_funding()',
                       'route.payload_positions.clone()', 'day_marker(volume.day_start)',
                       'get_sct_position()', 'transactions_by_height(height)',
                       'app.deferred_block_transactions', 'BlockTxIndexingMode::PerTx',
                       'BlockTxIndexingMode::DeferredBatch', 'fault in [1u8, 2u8]',
                       'effect_snapshot(&app, &[&first, &second]).await?, before']:
            self.assertIn(marker, self.source)
        self.assertIn('app.commit_for_testing', self.source)
        self.assertIn('compact.nullifiers.contains(&nullifier)', self.source)
        self.assertIn('compact.routing_actions.iter()', self.source)

    def test_claim_controls_decode_before_expected_crypto_failure(self):
        for marker in ['Claim::read_cfg', 'positive typed-claim encoding correspondence',
                       'changed.statement = claim.public_inputs[0].clone()',
                       'claim.commitments[0] += &G1::generator()',
                       'changed claim must decode', '"invalid Pari proof"',
                       '"invalid Pari proof batch"', '"wrong proof family"',
                       '"wrong proof relation"', '"wrong proof statement"',
                       '"mixed proof families"', '"empty proof batch"',
                       '"transfer proof context does not match its transaction location"']:
            self.assertIn(marker, self.source)
        self.assertNotIn('verify_prebound', self.source)
        self.assertNotIn('batch_verify_prebound', self.source)
        self.assertIn('expected_rejection', self.source)
        self.assertIn('wrong rejection cause:', self.source)

    def test_actual_capabilities_allow_row_permutation_but_refuse_slot_swap(self):
        for marker in ['registry().verify_items(items, &Sequential)?',
                       'slot-swap control must be nonvacuous',
                       'reversed.reverse()', 'capabilities[1].clone()',
                       'duplicate verified proof capability', 'verified proof-slot coverage mismatch',
                       'verified proof capability mismatch', 'cache.insert_fully_verified(bytes, verified.clone())?',
                       'cache.get(wrong_registry, &hash, bytes).is_none()',
                       'cache.get(registry().id(), &hash, &changed_bytes).is_none()',
                       'stateless cache artifact transaction does not match raw transaction']:
            self.assertIn(marker, self.source)
        self.assertTrue(any('wrong registry lookup' in contract for contract in self.manifest['source_contracts']))
        self.assertTrue(any('separately generated same-family' in contract for contract in self.manifest['source_contracts']))

    def test_warm_cache_current_state_control_is_independent_of_proof_mutation(self):
        name = 'genuine_transfer_cached_artifact_rechecks_volume_and_every_spend_slot'
        self.assertEqual(self.source.count('async fn ' + name + '('), 1)
        control = self.source.split('async fn ' + name + '(')[1]
        self.assertIn('spends.len(), 4', control)
        self.assertIn('0..=spends.len()', control)
        self.assertLess(control.index('probe.deliver_tx_bytes'), control.index('for stale_case'))
        self.assertLess(control.index('state.apply()'), control.index('expected_rejection('))
        for marker in ['assert_exact_transfer_effects(&probe, &tx)',
                       'state.record_volume_nullifier', 'state.nullify_all(&[nullifier]',
                       'was already spent in this block', 'is already spent for UTC day',
                       'Arc::ptr_eq(artifact, &cached)',
                       'effect_snapshot(&app, &[&tx]).await?, before',
                       'state rejection must not poison the valid stateless cache']:
            self.assertIn(marker, control)
        self.assertNotIn('verify_item', control)
        self.assertNotIn('insert_fully_verified', control)
        self.assertNotIn('commit_for_testing', control)
        self.assertNotIn('tx_bytes =', control)

    def test_distinct_registry_controls_reuse_native_setup_and_real_capabilities(self):
        descriptor = json.loads((ROOT / 'state/transfer_admission_controls.json').read_text())
        self.assertEqual(descriptor['status'], 'source_only_uncompiled_unrun')
        self.assertEqual(descriptor['evidence'], [])
        self.assertFalse(descriptor['certification'])
        self.assertEqual(descriptor['runtime_commit'], self.manifest['runtime_commit'])
        for key in ['setup_resource', 'test_append_resource', 'parent_control_resource']:
            self.assertEqual(hashlib.sha256((ROOT / descriptor[key]).read_bytes()).hexdigest(),
                             descriptor[key + '_sha256'])
        setup = (ROOT / descriptor['setup_resource']).read_text()
        self.assertEqual(setup.count('pari::setup('), 1)
        for marker in ['catalogue::compile(Family::Transfer)', 'rand10::rngs::SysRng',
                       '&Sequential', 'entry.family != Family::Transfer',
                       'pk.verifying_key() == &vk', 'Registry::load(&staging)',
                       'Registry::load(destination)', 'source artifact checksum mismatch',
                       'source registry path set is not complete/exact',
                       '[0u8; 65536]', 'create_new(true)', 'failed staging directory']:
            self.assertIn(marker, setup)
        controls = (ROOT / descriptor['test_append_resource']).read_text()
        for name in descriptor['tests']:
            self.assertEqual(controls.count('async fn ' + name.rsplit('::', 1)[1] + '('), 1)
        for marker in ['witness_auth_build(&plan, original.clone())',
                       'witness_auth_build(&plan, alternate.clone())',
                       'same completed plan/public statement', 'invalid Pari proof batch',
                       'proof capability registry mismatch', 'verified transaction registry mismatch',
                       'cross-artifact order control must be nonvacuous', 'swapped.reverse()',
                       'binding signature failed to verify', 'transfer auth signature failed to verify',
                       'std::mem::swap(body, &mut fee.transfer)',
                       'transfer proof context does not match its transaction location']:
            self.assertIn(marker, controls)
        self.assertNotIn('Verified {', controls)
        self.assertNotIn('without_proof', controls)


if __name__ == '__main__':
    unittest.main()
