"""Source composition controls, distinct from future real Rust control results."""
from pathlib import Path
import unittest

from integration.native_parameter_controls import append_controls


class NativeParameterControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = Path('C:/src/shieldd-pr160-844389ee/crates/crypto/primitives/src/poseidon.rs').read_bytes()
        cls.resource = (Path(__file__).resolve().parents[1] / 'integration/observers/native_parameter_loader_controls.rs').read_bytes()

    def test_only_new_cfg_test_delta_preserves_entire_parent_prefix(self):
        result = append_controls(self.source, self.resource)
        self.assertEqual(result[:len(self.source)], self.source)
        self.assertEqual(result[len(self.source):], self.resource)
        self.assertEqual(self.resource.count(b'#[test]'), 7)
        self.assertIn(b'native_values::<6>', self.resource)
        self.assertIn(b'native_values::<3>', self.resource)

    def test_changed_parent_and_double_append_refused(self):
        for wrong in [self.source + b'\n', append_controls(self.source, self.resource)]:
            with self.assertRaises(ValueError):
                append_controls(wrong, self.resource)

    def test_non_test_resource_and_missing_control_refused(self):
        for wrong in [self.resource.replace(b'#[cfg(test)]', b'#[cfg(any())]', 1),
                      self.resource.replace(b'#[test]', b'// missing test', 1)]:
            with self.assertRaises(ValueError):
                append_controls(self.source, wrong)


if __name__ == '__main__':
    unittest.main()
