import unittest
from pathlib import Path
from integration import balance_native_compile_repair as repair
from integration import balance_blinding_observer as observer

ROOT=Path(__file__).parents[1]
P=ROOT/'.work/diagnostics/transfer-implementation-20261002'


class NativeCompileRepairTests(unittest.TestCase):
    def test_actual_frozen_blinding_body_only_changes_the_module_path(self):
        before=(P/'balance-blinding-observer-source-08/overlay'/repair.BALANCE).read_bytes()
        after=repair.repair_balance(before)
        self.assertEqual(after.replace(b'crate::group::balance_blinding_fixed_inspection::scope(',b'group::balance_blinding_fixed_inspection::scope('),before)
        with self.assertRaises(ValueError):repair.repair_balance(after)
        source=(P/'balance-blinding-observer-source-08/anticipated-before'/repair.BALANCE).read_bytes()
        self.assertEqual(observer.instrument_balance(source),after)

    def test_fixture_production_prefix_and_field_arity_are_unchanged(self):
        after=(ROOT/'integration/observers/note_output_hash.rs').read_bytes()
        before=after.replace(b'.try_into().ok().expect("eight fixture note fields")',b'.try_into().unwrap()').replace(b'.try_into().ok().expect("seven fixture capsule fields")',b'.try_into().unwrap()')
        self.assertEqual(repair.repair_fixture(before),after)
        self.assertEqual(before.split(b'#[cfg(test)]')[0],after.split(b'#[cfg(test)]')[0])
        self.assertEqual(after.count(b'#[test]'),before.count(b'#[test]'))
        self.assertIn(b'values(8)',after);self.assertIn(b'values(7)',after)
        self.assertNotIn(b'derive(Debug)',after)
        self.assertEqual(repair.repair_fixture(before.replace(b'\n',b'\r\n')),after.replace(b'\n',b'\r\n'))
        with self.assertRaises(ValueError):repair.repair_fixture(after)

    def test_missing_or_production_array_conversion_refuses(self):
        with self.assertRaises(ValueError):repair.repair_fixture(b'#[cfg(test)] mod tests {}')
        sample=b'note:values(8).iter().map(observed).collect::<Vec<_>>().try_into().unwrap()\n#[cfg(test)] mod tests {}'
        with self.assertRaises(ValueError):repair.repair_fixture(sample)


if __name__=='__main__':unittest.main()
