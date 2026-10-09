"""Read-only hook preservation, exact-anchor refusal and bounded collector."""
from pathlib import Path
import unittest
from integration import recovery_hash_observer as observer,recovery_capsule_observer as capsule


class RecoveryHashObserverTests(unittest.TestCase):
    def test_recovery_hook_restores_the_same_operation_source(self):
        base=capsule.instrument_recovery(Path('tests/fixtures/current-recovery.rs').read_bytes(),
                                        Path('tests/fixtures/current-recovery-group.rs').read_bytes())
        fresh=observer.instrument_recovery(base)
        scope=b'    #[cfg(feature = "formal-observer")]\n    let _recovery_hash_scope = hash_inspection::scope();\n'
        restored=fresh.replace(b'#[cfg(feature = "formal-observer")]\npub mod hash_inspection;\n',b'').replace(scope,b'')
        self.assertEqual(restored,base.replace(b'\r\n',b'\n'))
        with self.assertRaises(ValueError):observer.instrument_recovery(fresh)
        with self.assertRaises(ValueError):observer.instrument_recovery(base.replace(b'capsule_inspection::scope()',b'capsule_inspection::begin()'))

    def test_hash_hooks_preserve_the_other_callbacks_and_lowering(self):
        base=(b'            let output_call = crate::note::output_hash_inspection::start(domain, inputs);\n'
              b'                crate::note::output_hash_inspection::state(&output_call, block, after, state);\n'
              b'            let output = self.hash(domain, inputs, |value| Var::native(value.clone()));\n'
              b'            crate::note::output_hash_inspection::finish(output_call, &output);\n')
        fresh=observer.instrument_hash(base)
        restored=b'\n'.join(line for line in fresh.split(b'\n') if b'recovery::hash_inspection' not in line)
        self.assertEqual(restored,base)
        with self.assertRaises(ValueError):observer.instrument_hash(fresh)
        with self.assertRaises(ValueError):observer.instrument_hash(base+base)
        with self.assertRaises(ValueError):observer.instrument_hash(base.replace(b'finish(output_call, &output)',b'finish(output_call)'))

    def test_collector_has_finite_inventory_exact_native_links_and_no_var_operations(self):
        source=Path('integration/observers/recovery_hash.rs').read_text()
        self.assertIn('s.reports.len()>=8',source);self.assertIn('s.slots>=2',source)
        self.assertIn('s.reports.len()==8',source);self.assertIn('s.calls!=4',source)
        self.assertIn('p.after.is_some()',source);self.assertIn('after.get(1)!=Some(&output)',source)
        self.assertIn('Observed::Native(Scalar::from(0))',source);self.assertIn('Observed::Native(Scalar::from(1))',source)
        self.assertIn('r.inputs==inputs && r.output==output',source)
        for operation in ('Var::witness','Var::native','canonical_bits','multiply_fixed','params.circuit'):
            self.assertNotIn(operation,source.split('#[cfg(test)]')[0])


if __name__=='__main__':unittest.main()
