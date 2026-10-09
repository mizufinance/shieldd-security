"""Source-bound asset-zero guard; this does not execute or certify runtime."""
from pathlib import Path
import re
import unittest

RUNTIME = Path('C:/src/shieldd-pr160-844389ee')
REPO = Path(__file__).resolve().parents[1]


class NativeAssetAdmissionTests(unittest.TestCase):
    def test_real_proof_api_rejects_zero_before_both_branch_reads(self):
        registry = (RUNTIME / 'crates/core/component/compliance/src/registry.rs').read_text()
        start = registry.index('async fn get_asset_proof_data(')
        body = registry[start:registry.index('\n    ///', start)]
        anchors = ['let value = asset_id.0;', 'value != Fq::from(0u64)',
                   '"asset value zero is reserved for sentinel leaf"',
                   'self.is_asset_regulated(asset_id).await?', 'if is_regulated {']
        self.assertEqual([body.index(x) for x in anchors], sorted(body.index(x) for x in anchors))
        query = (RUNTIME / 'crates/core/component/compliance/src/component/query.rs').read_text()
        status = query[query.index('pub async fn compliance_asset_status('):]
        self.assertIn('.get_asset_proof_data(asset_id)\n        .await\n        .map_err(', status)

    def test_sdk_witness_has_separate_gap_and_regulated_membership_semantics(self):
        source = (RUNTIME / 'crates/core/component/shielded-pool/src/action_context.rs').read_text()
        start = source.index('pub fn validate(&self, asset_id: asset::Id, sender: &Address)')
        body = source[start:source.index('pub fn validate_user(', start)]
        self.assertIn('self.asset.leaf.value == asset_id.0', body)
        self.assertIn('"unregulated asset witness must prove non-membership"', body)
        self.assertIn('.cmp(asset_id.0.to_bytes().iter().rev())\n                    .is_lt()', body)
        # Canonical unsigned little-endian bytes cannot have a predecessor below zero.
        zero = bytes(32)
        for value in (0, 1, 17, 2**254):
            self.assertFalse(value.to_bytes(32, 'little')[::-1] < zero[::-1])
        # The guarded proof API and arbitrary supplied regulated membership differ.
        self.assertNotIn('asset_id.0 != Fq::from(0u64)', body)
        registry = (RUNTIME / 'crates/core/component/compliance/src/registry.rs').read_text()
        self.assertIn('"genesis asset ID zero is reserved"', registry)
        self.assertIn('"IMT insert failed: zero value is reserved for sentinel leaf"', registry)

    def test_handwritten_boundary_exports_only_independent_admission(self):
        source = (REPO / 'circuits/ShielddSecurity/NativeAssetAdmission.lean').read_text()
        exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
        self.assertEqual(len(exports), 4)
        self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
        self.assertEqual(source.count('set_option pp.all true in'), 4)
        self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('set_option maxHeartbeats 150000', source)
        self.assertIn('set_option maxRecDepth 2048', source)
        self.assertIn('simp only [proofDataNative,zero,if_true] at accepted\n  cases accepted', source)
        self.assertIn('simp only [proofDataNative,if_true]', source)
        self.assertNotIn('Satisfies', source)
        self.assertNotIn('inverseEquation', source)


if __name__ == '__main__':
    unittest.main()
