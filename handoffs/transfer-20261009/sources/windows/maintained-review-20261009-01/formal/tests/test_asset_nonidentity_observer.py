"""Tiny source correspondence checks; native compile and row replay separate."""
from pathlib import Path
import unittest
from integration import asset_nonidentity_observer as observer, asset_hash_observer

ROOT=Path(__file__).resolve().parents[1]
RES=ROOT/'integration/observers'


class AssetNonidentityObserverTests(unittest.TestCase):
    def test_original_nonidentity_and_prior_callbacks_remain_exact(self):
        group=(ROOT/'tests/fixtures/current-recovery-group.rs').read_bytes()
        anchor=b'        let _ = self.x.inv();'
        old=b'''        let _inverse = self.x.inv();
        #[cfg(feature = "formal-observer")]
        inspection::record_nonidentity(&self.x, &_inverse);
        #[cfg(feature = "formal-observer")]
        ownership_inspection::nonidentity(&self.x, &_inverse);'''
        group=group.replace(anchor,old)
        result=observer.instrument_group(group)
        hook=b'\n        #[cfg(feature = "formal-observer")]\n        crate::balance::asset_nonidentity_inspection::record(&self.x, &_inverse);'
        self.assertEqual(result.replace(hook,b''),group)
        self.assertEqual(result.count(b'let _inverse = self.x.inv();'),1)
        with self.assertRaises(ValueError):observer.instrument_group(result)
        with self.assertRaises(ValueError):observer.instrument_group(group.replace(b'self.x.inv()',b'self.y.inv()'))

    def test_balance_scope_preserves_operations_and_line_endings(self):
        original=asset_hash_observer.compose_observed_balance((ROOT/'tests/fixtures/current-observed-balance.rs').read_bytes()).replace(b'\r\n',b'\n')
        result=observer.instrument_balance(original)
        hook=b'''    #[cfg(feature = "formal-observer")]
    let nonidentity_scope = asset_nonidentity_inspection::scope(asset, &hash, &generator);
'''
        finish=b'\n    #[cfg(feature = "formal-observer")]\n    drop(nonidentity_scope);'
        header=b'#[cfg(feature = "formal-observer")]\npub mod asset_nonidentity_inspection;\n'
        self.assertEqual(result.removeprefix(header).replace(hook,b'').replace(finish,b''),original)
        order=[b'drop(asset_scope);',b'let nonidentity_scope',b'generator.assert_non_identity();',b'drop(nonidentity_scope);',b'for value in inputs.iter()']
        self.assertEqual([result.index(v) for v in order],sorted(result.index(v) for v in order))
        self.assertEqual(observer.instrument_balance(original.replace(b'\n',b'\r\n')),result.replace(b'\n',b'\r\n'))
        with self.assertRaises(ValueError):observer.instrument_balance(result)
        with self.assertRaises(ValueError):observer.instrument_balance(original.replace(b'drop(asset_scope);',b'drop(other_scope);'))

    def test_bounded_one_compile_and_strict_qualification_dispatch(self):
        catalogue=(RES/'asset_map_catalogue.rs').read_bytes(); result=observer.catalogue(catalogue)
        self.assertEqual(result.count(b'circuit::build('),1);self.assertEqual(result.count(b'Relation::compile_inspected('),1)
        self.assertIn(b'nonidentity.generator == report.cofactor[3]',result)
        self.assertIn(b'.chain(nonidentity.selected())',result)
        exporter=observer.exporter((RES/'asset_map_export.rs').read_bytes())
        qualifier=(RES/'asset_nonidentity_qualification.rs').read_bytes()
        # The old source has the same immutable dispatch anchors as merged05.
        from integration.asset_map_observer import instrument_exporter
        base=instrument_exporter((ROOT/'tests/fixtures/current-transfer-ownership-inspection.rs').read_bytes(),(RES/'asset_map_export.rs').read_bytes())
        # Supply the current maintained T4 dispatch branch used by both appends.
        base=base.replace(b'        Some("shieldd-transfer-fixed-spend-v1")',b'        Some("shieldd-transfer-t4-pages-v1") |\n        Some("shieldd-transfer-fixed-spend-v1")')
        base=base.replace(b'            anyhow::ensure!(\n                pending["repeated_observations_equal"]',b'            if pending["schema"] == "shieldd-transfer-t4-pages-v1" {\n                qualify_transfer_t4_pages(first,repeated,&pending)?;\n            }\n            anyhow::ensure!(\n                pending["repeated_observations_equal"]')
        combined=observer.instrument_exporter(base,exporter,qualifier)
        self.assertIn(b'args[0]=="asset-nonidentity-spool"',combined)
        self.assertIn(b'fn capture_asset_map(',combined)
        self.assertEqual(combined.count(b'compare_framed_rows(&paths[0], path, 200770, 262144)?;'),1)
        self.assertLess(combined.index(b'pending == repeat'),combined.index(b'qualify_asset_nonidentity(&pending)?'))
        self.assertIn(b'object.len()==keys.len()',qualifier)
        self.assertIn(b'n["generator"]==p["cofactor"][3]',qualifier)
        self.assertIn(b'i[0]==1',qualifier)
        with self.assertRaises(ValueError):observer.instrument_exporter(combined,exporter,qualifier)
        with self.assertRaises(ValueError):observer.catalogue(catalogue.replace(b'report, selected, expressions',b'report, expressions, selected'))
        resource=(RES/'asset_nonidentity.rs').read_bytes()
        for operation in (b'.inv()',b'Var::witness(',b'.assert_eq('):self.assertNotIn(operation,resource)
        self.assertIn(b's.entered==1',resource);self.assertIn(b's.scope.is_none()',resource)
        self.assertIn(b'pub fn scope<\'ctx>',resource);self.assertIn(b'pub fn record<\'ctx>',resource)


if __name__=='__main__':unittest.main()
