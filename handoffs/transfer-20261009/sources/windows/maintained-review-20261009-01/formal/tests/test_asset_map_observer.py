"""Fresh source hooks and drift refusals; runtime row parity is separate."""
from pathlib import Path
import unittest
from integration.asset_map_observer import instrument_map, instrument_balance, instrument_encoding, instrument_catalogue, instrument_exporter

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/fixtures'


class AssetMapObserverTests(unittest.TestCase):
    def test_native_map_and_unowned_code_are_byte_preserved(self):
        original = (FIXTURES / 'current-asset-map.rs').read_bytes()
        out = instrument_map(original)
        begin = original.index(b"pub fn circuit<'ctx>(")
        end = original.index(b'\npub fn asset(', begin)
        prefix = b'#[cfg(feature = "formal-observer")]\npub mod asset_inspection;\n'
        native_end = original.index(b'/// Unique QR choice:')
        self.assertTrue(out.startswith(prefix + original[:native_end]))
        self.assertTrue(out.endswith(original[end:]))
        self.assertEqual(out.count(b'asset_inspection::record('), 1)
        self.assertIn(b'let y_bits = encoding::canonical_bits(ctx, &y);', out)
        self.assertIn(b'for _ in 0..3 {\n        let xx = point.x.clone() * &point.x;', out)
        self.assertIn(b'let divisor = plus.clone() * &minus;', out)
        self.assertIn(b'asset_inspection::qr(&squared, &selected);', out)
        for statement in (b'constrain_square(&gx1, &square, &qr_root);',
                          b'let y_square = y.clone() * &y;',
                          b'y_square.assert_eq(&y_squared);',
                          b'inverse_product.assert_eq(&(Var::one() - zero.var()));',
                          b'inverse_zero.assert_eq(&Var::zero());'):
            self.assertIn(statement, out)

    def test_arithmetic_drift_and_repeat_refused(self):
        original = (FIXTURES / 'current-asset-map.rs').read_bytes()
        with self.assertRaises(ValueError): instrument_map(instrument_map(original))
        for before, after in ((b'encoding::canonical_bits(ctx, &y)[0]', b'encoding::canonical_bits(ctx, &y)[1]'),
                              (b'(denominator * zero.var())', b'(denominator + zero.var())'),
                              (b'for _ in 0..3 {', b'for _ in 0..2 {'),
                              (b'&Var::native(c2),', b'&Var::native(c1),')):
            with self.subTest(before=before), self.assertRaises(ValueError):
                instrument_map(original.replace(before, after))

    def test_balance_hash_and_scope_remain_in_order(self):
        original = (FIXTURES / 'current-asset-balance.rs').read_bytes()
        out = instrument_balance(original)
        self.assertIn(b'let hash = params.circuit(map::ASSET_GENERATOR, &[asset.clone()]);', out)
        self.assertLess(out.index(b'let asset_scope'), out.index(b'let generator = map::circuit'))
        self.assertLess(out.index(b'drop(asset_scope);'), out.index(b'generator.assert_non_identity();'))
        self.assertTrue(out.endswith(original[original.index(b'    generator.assert_non_identity();'):]))
        with self.assertRaises(ValueError): instrument_balance(out)
        with self.assertRaises(ValueError): instrument_balance(original.replace(b'ASSET_GENERATOR', b'UNREGULATED_RING'))

    def test_line_endings_and_pending_full_spool_qualification(self):
        source = (FIXTURES / 'current-asset-map.rs').read_bytes()
        self.assertEqual(instrument_map(source.replace(b'\n', b'\r\n')),
                         instrument_map(source).replace(b'\n', b'\r\n'))
        with self.assertRaises(ValueError): instrument_map(source.replace(b'\n', b'\r\n', 1))
        catalogue = instrument_catalogue(b'// sentinel\n')
        with self.assertRaises(ValueError): instrument_catalogue(catalogue)
        exporter = (FIXTURES / 'current-transfer-ownership-inspection.rs').read_bytes()
        fragment = (ROOT / 'integration/observers/asset_map_export.rs').read_bytes()
        result = instrument_exporter(exporter, fragment)
        self.assertEqual(result.count(b'args[0] == "asset-map-spool"'), 1)
        self.assertIn(b'"ordinary_full_ordered_rows_equal":false', result)
        self.assertIn(b'compare_framed_rows(&paths[0], path, 200770, 262144)', result)
        self.assertIn(b'pending == repeat', result)
        with self.assertRaises(ValueError): instrument_exporter(result, fragment)

    def test_canonical_source_keeps_reconstruction_and_strict_bound(self):
        source = (FIXTURES / 'current-asset-encoding.rs').read_bytes()
        result = instrument_encoding(source)
        anchor = source.index(b'    less_or_equal(bits, &maximum).assert_eq(&BoolVar::constant(true));')
        self.assertTrue(result.startswith(source[:anchor]))
        self.assertIn(b'bounded.assert_eq(&BoolVar::constant(true));', result)
        self.assertIn(b'asset_inspection::canonical(value, bits, &sum, &bounded);', result)
        with self.assertRaises(ValueError): instrument_encoding(result)
        with self.assertRaises(ValueError): instrument_encoding(source.replace(b'less_or_equal(bits, &maximum)', b'less_or_equal(&maximum, bits)'))


if __name__ == '__main__': unittest.main()
