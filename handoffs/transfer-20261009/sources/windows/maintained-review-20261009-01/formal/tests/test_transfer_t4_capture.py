"""Future source ordering, bounded inventory and unchanged full-row qualifier."""
import unittest
from pathlib import Path
from integration import asset_hash_observer as asset,asset_map_observer as maps,transfer_t4_capture as capture

ROOT=Path(__file__).resolve().parents[1]


class TransferT4CaptureTests(unittest.TestCase):
    def test_asset_hash_wrap_preserves_original_and_existing_map_scope(self):
        original=(ROOT/'tests/fixtures/current-asset-balance.rs').read_bytes()
        for source in (original,maps.instrument_balance(original)):
            result=asset.instrument_balance(source)
            added_before=(b'    #[cfg(feature = "formal-observer")]\n'
                b'    let asset_hash_scope = crate::hash::asset_hash_inspection::scope(asset);\n')
            added_after=(b'\n    #[cfg(feature = "formal-observer")]\n'
                b'    crate::hash::asset_hash_inspection::finish_scope(asset_hash_scope, &hash);')
            self.assertEqual(result.replace(added_before,b'').replace(added_after,b''),source)
            self.assertLess(result.index(b'asset_hash_inspection::scope'),result.index(b'params.circuit(map::ASSET_GENERATOR'))
            self.assertLess(result.index(b'asset_hash_inspection::finish_scope'),result.index(b'let generator = map::circuit'))
            with self.assertRaises(ValueError):asset.instrument_balance(result)
        with self.assertRaises(ValueError):asset.instrument_balance(original.replace(b'ASSET_GENERATOR',b'NOTE'))

    def test_combined_balance_retains_current_balance_mode_and_all_existing_operations(self):
        original=(ROOT/'tests/fixtures/current-observed-balance.rs').read_bytes()
        result=asset.compose_observed_balance(original)
        # Remove only the new cfg-only scopes. The entire old signed/scalar/
        # balance operation body and its observer module must remain identical.
        normalized=lambda data:data.replace(b'\r\n',b'\n')
        restored=normalized(result)
        for addition in (
            b'    #[cfg(feature = "formal-observer")]\n    let asset_hash_scope = crate::hash::asset_hash_inspection::scope(asset);\n',
            b'\n    #[cfg(feature = "formal-observer")]\n    crate::hash::asset_hash_inspection::finish_scope(asset_hash_scope, &hash);',
            b'    #[cfg(feature = "formal-observer")]\n    let asset_scope = map::asset_inspection::scope(asset, &hash);\n',
            b'\n    #[cfg(feature = "formal-observer")]\n    drop(asset_scope);'):
            restored=restored.replace(addition,b'')
        self.assertEqual(restored,normalized(original))
        self.assertEqual(result.count(b'pub mod inspection {'),1)
        self.assertEqual(result.count(b'inspection::record("signed",'),1)
        with self.assertRaises(ValueError):asset.compose_observed_balance(result)
        with self.assertRaisesRegex(ValueError,'existing observer'):
            asset.compose_observed_balance((ROOT/'tests/fixtures/current-asset-balance.rs').read_bytes())

    def test_combined65_keeps_old55_callback_and_lowering_and_refuses_source_drift(self):
        base=(ROOT/'integration/observers/note_t4_pages_catalogue.rs').read_bytes()
        cones=(ROOT/'integration/observers/transfer_t4_hash_cones.rs').read_bytes()
        result=capture.catalogue(base,cones)
        start=base.index(b'            if ordinal < 55 {');end=base.index(b'            } else {',start)
        old=base[start:end].replace(b'NoteT4Page',b'TransferT4Page')
        self.assertIn(old,result)
        self.assertEqual(result.count(b'circuit::build('),1)
        self.assertEqual(result.count(b'Relation::compile_inspected_pages'),1)
        self.assertIn(b'        65,',result);self.assertIn(b'pages.len() == 65',result)
        self.assertIn(b'ordinal < 63',result);self.assertIn(b'ordinal == 63',result);self.assertIn(b'ordinal == 64',result)
        self.assertIn(b'asset_map.values[0] == asset_map.hash',result)
        self.assertIn(b'output.note[2] == asset_hash.asset',result)
        self.assertNotIn(b'output.note[0] == asset_hash.asset',result)
        self.assertIn(b'selected.len() <= 4096',result)
        self.assertIn(b'roots.contains(&index)',result)
        self.assertIn(b'undeclared actual permutation witness',result)
        with self.assertRaises(ValueError):capture.catalogue(base.replace(b'        56,',b'        57,'),cones)

    def test_exporter_preserves_ordinary2_repeat_and_exact_native_page_inventory(self):
        source=(ROOT/'integration/observers/note_t4_pages_export.rs').read_bytes()
        serialization=(ROOT/'integration/observers/transfer_t4_pages_serialization.rs').read_bytes()
        fragment=capture.exporter(source,serialization)
        base=(ROOT/'integration/src/bin/transfer-ownership-inspection.rs').read_bytes()
        exporter=capture.instrument_exporter(base,fragment)
        self.assertEqual(exporter.count(b'compare_framed_rows(&paths[0], path, 200770, 262144)?;'),1)
        self.assertEqual(exporter.count(b'pending == repeat'),1)
        self.assertIn(b'qualify_note_hash_pages(first,repeated,&input)?',exporter)
        for token in (b'bytes==repeat',b'pages.len()==65',b'55..=62',b'63=>Ok((0,"asset",0,0))',
            b'64=>Ok((0,"roles",0,0))',b'"shieldd-transfer-note-output-hash-block-v1",20,7,6,2',
            b'"shieldd-transfer-asset-hash-block-v1",26,1,3,1',b'count == 65',b'count < 65',b'0..65',
            b'"ordinary_full_ordered_rows_equal":false',b'"repeated_observations_equal":false',
            b'/tree/spend',b'page.tree_handles.contains(source)'):
            self.assertIn(token,exporter)
        self.assertIn(b'"page{ordinal}.observations.json"',exporter)
        self.assertLess(exporter.index(b'write_packet_json(prefix, &format!("page{ordinal}.observations.json")'),
            exporter.index(b'count += 1;',exporter.index(b'fn capture_transfer_t4_pages')))
        with self.assertRaises(ValueError):capture.instrument_exporter(exporter,fragment)

    def test_packet_digest_uses_existing_reexport_without_new_direct_dependency(self):
        base=(ROOT/'integration/src/bin/transfer-ownership-inspection.rs').read_text()
        self.assertEqual(base.count('fn packet_blake3('),1)
        self.assertIn('use commonware_cryptography::blake3::CoreBlake3;',base)
        helper=base[base.index('fn packet_blake3('):base.index('fn index(')]
        for step in ('CoreBlake3::new()','hasher.update(bytes)','hasher.finalize().to_hex().to_string()'):
            self.assertIn(step,helper)
        self.assertNotIn('blake3::hash(',base)
        self.assertEqual(base.count('packet_blake3(&bytes)'),5)
        fragment=capture.exporter((ROOT/'integration/observers/note_t4_pages_export.rs').read_bytes(),
            (ROOT/'integration/observers/transfer_t4_pages_serialization.rs').read_bytes())
        self.assertEqual(fragment.count(b'packet_blake3(&bytes)'),2)
        self.assertNotIn(b'blake3::hash(',fragment)
        self.assertIn(b'bytes==repeat',fragment)


if __name__=='__main__':unittest.main()
