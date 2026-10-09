"""Tiny source checks only; no native witness, proof or branch coverage claim."""
import hashlib
import json
from pathlib import Path
import re
import runpy
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class TransferBranchMatrixTests(unittest.TestCase):
    def setUp(self):
        self.m = json.loads((ROOT / 'state/transfer_branch_matrix.json').read_bytes())
        self.source = (ROOT / self.m['resource']).read_text()

    def test_closed_roster_identity_and_open_status(self):
        m = self.m
        self.assertEqual(m['runtime_commit'], json.loads((ROOT / 'shieldd.lock').read_bytes())['sha'])
        self.assertEqual(m['status'], 'source_only_uncompiled_unrun')
        self.assertFalse(m['certification'])
        self.assertEqual(m['evidence'], [])
        self.assertEqual(hashlib.sha256((ROOT / m['resource']).read_bytes()).hexdigest(), m['resource_sha256'])
        source_roster = re.findall(r'"([a-z_]+)"', self.source.split('const CASES:')[1].split('];')[0])
        self.assertEqual(source_roster, [x['case'] for x in m['cases']])
        self.assertEqual(len(set(source_roster)), 17)
        self.assertTrue(all(x['status'] == 'UNRUN' and x['genuine_receipt'] is None for x in m['cases']))

    def test_native_proof_and_bounded_constructor_are_required(self):
        s = self.source
        for token in ['fixtures::build(p, g, &f)', 'catalogue::Witness::Transfer(Box::new(w))',
                      'registry.prove(&native, &Sequential)', 'Envelope::from_bytes(&envelope.to_bytes())',
                      'registry.verify(Family::Transfer, &digest, &decoded)', 'for seed in 0..32u8',
                      'word[31] & 1 == 1', 'bounded native permutation search exhausted',
                      'input0.overflowing_add(input1)', 'outbound.overflowing_add(change)',
                      'input_sum == output_sum']:
            self.assertIn(token, s)
        self.assertLess(s.index('registry.verify('), s.index('println!("BRANCH_GENUINE_PASS'))
        for bad in ['Verified::', 'without_proof', 'unsafe ', 'pari::setup', 'mock_proof']:
            self.assertNotIn(bad, s)

    def test_fee_fixture_limit_and_exact_native_construction(self):
        s = self.source
        fee = s.split('if name == "fee_funding" {', 2)[2].split('if wanted.', 1)[0]
        for token in ['w.volume.proof_context == 2', '!w.volume.use_real',
                      'w.volume.nullifier = Scalar::from(0)',
                      'w.volume.commitment = Scalar::from(0)', 'w.volume.day_start = Scalar::from(0)']:
            self.assertIn(token, fee)
        self.assertIn('Pinned fixtures::build chooses Ordinary', self.m['fixture_limitation'])
        self.assertIn('not native wallet completion', self.m['scope'])

    def test_independent_expected_branch_matrix(self):
        by_case = {x['case']: x['expected_observation'] for x in self.m['cases']}
        for x in by_case.values():
            self.assertEqual(int(x['input0']) + int(x['input1']), int(x['outbound']) + int(x['change']))
            self.assertGreater(int(x['outbound']), 0)
            self.assertEqual(x['eligible'], x['proof_context'] == 1 and x['regulated'] and not x['same_address'])
            self.assertEqual(x['flagged'], x['eligible'] and not x['use_real'])
            self.assertLessEqual(x['regulated_precision'], x['unregulated_precision'])
            self.assertLessEqual(x['unregulated_precision'], 32)
            self.assertEqual(x['second'], x['timestamp'] % 86400)
            self.assertEqual(x['day_index'], x['timestamp'] // 86400)
            if x['use_real']:
                self.assertEqual(int(x['prior']) + int(x['outbound']), int(x['successor']))
        self.assertFalse(by_case['real_second']['optional_dummy'])
        self.assertTrue(by_case['self_transfer']['same_address'])
        self.assertEqual(by_case['fee_funding']['proof_context'], 2)
        self.assertEqual(by_case['zero_change']['change'], '0')
        self.assertEqual(by_case['nonzero_continuation']['prior'], '5')
        self.assertEqual(by_case['amount_max']['outbound'], str(2**128 - 1))
        self.assertTrue(by_case['amount_sum_max']['input_sum_carry'])
        self.assertEqual(by_case['amount_sum_max']['input_sum_low'], str(2**128 - 2))
        self.assertEqual({by_case[n]['permutation'] for n in ['permutation_zero', 'permutation_one']}, {False, True})

    def test_api_controls_separate_from_proof_and_exact_source_predicates(self):
        for token in ['[(33, 33), (8, 7)]', 'contains("routing precision")',
                      'Scalar::from_limbs([0, 0, 1, 0])', 'contains("amount exceeds u128")']:
            self.assertIn(token, self.source)
        self.assertEqual(len(self.m['branches']), 13)
        for branch in self.m['branches']:
            self.assertIn(branch['case'], [x['case'] for x in self.m['cases']])
            self.assertEqual(branch['status'], 'source_read_runtime_UNRUN')
            self.assertGreater(branch['line'], 0)
            self.assertTrue(branch['exact_source_predicate'])

    def test_derivative_stage_source_guard_refuses_mutations(self):
        # Importing the deferred helper does not activate its main entry point.
        packet = ROOT / '.work/diagnostics/transfer-implementation-20261002/transfer-branch-matrix-prepare-02'
        if not (packet / 'stage.py').is_file():
            self.skipTest('local immutable source-stage packet is not a repository dependency')
        helper = runpy.run_path(str(packet / 'stage.py'))
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            scopes = {}
            for kind, relative in [('sdk', 'crates/crypto/circuits/src/example.rs'),
                                   ('compiler', 'third_party/commonware/cryptography/src/zk/example.rs'),
                                   ('app', 'crates/core/app/src/example.rs'),
                                   ('exporters', 'crates/crypto/circuits/examples/example.rs')]:
                path = base / relative
                path.parent.mkdir(parents=True)
                path.write_bytes(b'exact owned source\n')
                scopes[kind] = {relative: helper['digest'](path)}
            helper['verify_scope'](base, scopes, {})
            changed = base / next(iter(scopes['sdk']))
            changed.write_bytes(b'changed owned source\n')
            with self.assertRaisesRegex(ValueError, 'parent source mismatch'):
                helper['verify_scope'](base, scopes, {})
            changed.write_bytes(b'exact owned source\n')
            extra = changed.with_name('unreviewed.rs')
            extra.write_bytes(b'unreviewed\n')
            with self.assertRaisesRegex(ValueError, 'path-set mismatch'):
                helper['verify_scope'](base, scopes, {})
            extra.unlink()
            with self.assertRaisesRegex(ValueError, 'parent source mismatch'):
                helper['verify_scope'](base, scopes, {'Cargo.lock': '0' * 64})


if __name__ == '__main__':
    unittest.main()
