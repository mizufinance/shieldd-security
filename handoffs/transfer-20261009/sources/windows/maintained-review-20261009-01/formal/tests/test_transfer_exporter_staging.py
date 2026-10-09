from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

import security
from integration.staging import EXPORTERS, _inventory, prepare_exporters


class ExporterStagingTests(unittest.TestCase):
    def fixture(self, root):
        source, stage = root / 'source', root / 'stage'
        for base in (source, stage):
            for name in ('Cargo.toml', 'Cargo.lock', 'crates/crypto/circuits/Cargo.toml',
                         'third_party/commonware/Cargo.lock',
                         'third_party/commonware-patches/provenance.json',
                         'crates/crypto/circuits/src/lib.rs',
                         'crates/crypto/primitives/src/lib.rs',
                         'crates/crypto/primitives/params/wide',
                         'third_party/commonware/cryptography/src/zk/circuit.rs'):
                path = base / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(name)
        return source, stage

    def test_exact_copy_is_idempotent_and_preserves_locks(self):
        with tempfile.TemporaryDirectory() as directory:
            source, stage = self.fixture(Path(directory))
            result = prepare_exporters(source, stage)
            self.assertEqual(result, prepare_exporters(source, stage))
            self.assertEqual(set(result['exporters']), set(EXPORTERS))
            self.assertEqual(result['selected_source_inventories']['crates/crypto/circuits/src']['files'], 1)
            self.assertIn('no build', result['scope'])
            self.assertIn('transfer-baseline', result['exporters'])
            baseline = (stage / 'crates/crypto/circuits/examples/transfer-baseline.rs').read_text()
            self.assertIn('#[cfg(shieldd_formal_example)]', baseline)
            self.assertIn('#[path = "../src/fixtures.rs"]', baseline)
            self.assertIn('full_ordered_relation_rows_equal', baseline)
            self.assertEqual((source / 'Cargo.lock').read_bytes(),
                             (stage / 'Cargo.lock').read_bytes())

    def test_lock_and_source_mismatch_refuse_before_writes(self):
        for name in ('Cargo.lock', 'crates/crypto/circuits/src/lib.rs'):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                source, stage = self.fixture(Path(directory))
                (stage / name).write_text('divergent')
                with self.assertRaisesRegex(ValueError, 'mismatch'):
                    prepare_exporters(source, stage)
                self.assertFalse((stage / 'crates/crypto/circuits/examples').exists())

    def test_git_checkout_and_divergent_exporter_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            source, stage = self.fixture(Path(directory))
            (stage / '.git').write_text('gitdir: elsewhere')
            with self.assertRaisesRegex(ValueError, 'disposable'):
                prepare_exporters(source, stage)
            (stage / '.git').unlink()
            target = stage / 'crates/crypto/circuits/examples/transfer-relation.rs'
            target.parent.mkdir()
            target.write_text('preexisting divergent source')
            with self.assertRaisesRegex(ValueError, 'divergent'):
                prepare_exporters(source, stage)
            self.assertEqual(target.read_text(), 'preexisting divergent source')

    def test_nested_directory_symlink_is_not_silently_skipped(self):
        with tempfile.TemporaryDirectory() as directory:
            source, _ = self.fixture(Path(directory))
            link = Mock()
            link.is_symlink.return_value = True
            link.is_file.return_value = False
            with patch.object(Path, 'rglob', return_value=[link]):
                with self.assertRaisesRegex(ValueError, 'symbolic links'):
                    _inventory(source, 'crates/crypto/circuits/src')

    def test_cli_rejects_qualification_and_calls_staging_only(self):
        with patch.object(security, 'check_register', return_value={}), \
                patch('integration.staging.prepare_exporters', return_value={'scope': 'diagnostic'}) as prepare:
            with patch('sys.argv', ['security.py', 'check', '--exporter-stage', 'stage',
                                    '--qualified-receipts', 'receipt']):
                self.assertEqual(security.main(), 1)
                prepare.assert_not_called()
            with patch('sys.argv', ['security.py', 'check', '--source', 'source',
                                    '--exporter-stage', 'stage']):
                self.assertEqual(security.main(), 0)
                prepare.assert_called_once_with(Path('source'), Path('stage'))


if __name__ == '__main__':
    unittest.main()
