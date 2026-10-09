"""Exact owned source association/refusal, not SDK or Lean verification."""
import unittest
from pathlib import Path
import ast,json,hashlib
from circuits import generate_transfer_balance_asset_seed_reuse as reuse, transfer_relation as relation


class NativeAssetValueGeneratorSourceTests(unittest.TestCase):
    def test_root_route_preserves_real_parent_reacceptance_and_conditional_scope(self):
        p=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
        packet=p/'balance-asset-seed-reuse-source-01'
        manifest=json.loads((packet/'manifest.json').read_bytes())
        for relative,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((packet/relative).read_bytes()).hexdigest(),digest)
        driver=(packet/'driver.py').read_text()
        ast.parse(driver)
        self.assertIn('actual.restore_caller',driver)
        self.assertIn('reuse.generate(',driver)
        self.assertNotIn("spec['ordinary']",driver)
        self.assertIn('cargo-future-asset-qualify-07/stdout.txt',driver)
        self.assertIn('NOT full closure credit',driver)
        recipe=json.loads((p/'balance-asset-seed-reuse-root-recipe-01.json').read_bytes())
        self.assertEqual((recipe['modules'],recipe['exports'],recipe['ordinary_stream_reads']),(2,7,0))
        self.assertFalse(recipe['qualification'])
        self.assertIn('domain18',recipe['owned_source_obligations']['hash'])
        self.assertIn('owned proof obligation',recipe['owned_source_obligations']['map'])
        preparer=(p/'prepare-balance-asset-seed-reuse-kernel-01.py').read_text()
        ast.parse(preparer)
        self.assertIn("b'0\\r\\n'",preparer)
        self.assertIn("before!=json.loads",preparer)

    def test_unqualified_sources_refuse_without_generating_a_candidate(self):
        with self.assertRaises(relation.RelationError):
            reuse.generate(b'{}\n', [], {}, [], b'{}\n', {})

    def test_owned_native_method_has_exact_domain_arity_and_no_retry(self):
        root = Path('C:/src/shieldd-pr160-844389ee')
        source = (root/'crates/core/asset/src/asset/id.rs').read_text()
        body = source.split('pub fn value_generator(&self)', 1)[1].split('/// Convert the asset ID', 1)[0]
        self.assertIn('map::to_subgroup(&shieldd_sdk_crypto::poseidon::hash(', body)
        self.assertIn('domains::ASSET_GENERATOR,', body)
        self.assertIn('&[self.0],', body)
        for token in ('loop', 'retry', 'is_identity'):
            self.assertNotIn(token, body)
        self.assertIn('pub const ASSET_GENERATOR: u8 = 26;',
                      (root/'crates/crypto/primitives/src/domains.rs').read_text())
        proof = Path('C:/src/shieldd-formal/circuits/ShielddSecurity/NativeAssetValueGenerator.lean').read_text()
        self.assertIn('abi.toSubgroup (abi.poseidon 26 [asset])', proof)
        self.assertEqual(proof.count('#print axioms '), 3)
        self.assertEqual(proof.count('#check @'), 3)
        self.assertIn('hashMeaning : ∀ asset : Q', proof)
        self.assertIn('mapMeaning : ∀ input : Q', proof)
