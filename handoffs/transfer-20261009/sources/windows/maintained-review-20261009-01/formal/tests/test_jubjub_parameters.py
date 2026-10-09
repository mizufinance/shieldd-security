"""Finite certificate/source-binding controls, not a Lean or native-field proof."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'circuits'))
import generate_jubjub as gj


class JubjubParameterControls(unittest.TestCase):
    def test_elligator_nonsquares_and_source_mutations(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            curve = root / 'crates/crypto/circuits/src/group.rs'
            field = root / 'third_party/commonware/cryptography/src/bls12381/primitives/group.rs'
            mapped = root / 'crates/crypto/circuits/src/map.rs'
            curve.parent.mkdir(parents=True)
            field.parent.mkdir(parents=True)
            curve.write_text('pub fn coefficient_d() -> Scalar { -Scalar::from(10240) * &Scalar::from(10241).inv() }')
            field.write_text(f'/// r = 0x{gj.P:x}\npub struct Scalar(pub(crate) blst_fr);')
            source = '''fn coefficients() -> (Scalar, Scalar, Scalar) {
              let k = -Scalar::from(40964); let inverse = k.inv();
              (k, Scalar::from(40962) * &inverse, inverse.clone() * &inverse,)
            }
            let tv = z.clone() * u * u;
            let x1 = -c1.clone() * &(F::one() + &tv).inv();
            let gx1 = ((x1.clone() + c1) * &x1 + c2) * &x1;
            let x2 = -x1.clone() - c1; let gx2 = tv * &gx1;
            x_coordinates(u, &c1, &c2, &Scalar::from(5));
            Var::native(Scalar::from(5)); Var::native(Scalar::from(5));'''
            mapped.write_text(source)
            bases, _ = gj.map_parameters(root)
            self.assertEqual(bases['z'], 5)
            self.assertEqual(bases['negative_z'], gj.P - 5)
            for value in bases.values():
                self.assertEqual(pow(value, (gj.P-1)//2, gj.P), gj.P-1)
            for mutation in (source.replace('40964', '40965'),
                             source.replace('40962', '40961'),
                             source.replace('tv * &gx1', 'tv * tv * &gx1'),
                             source.replace('-x1.clone() - c1', '-x1.clone() + c1'),
                             source.replace('from(5)', 'from(4)'), source + source):
                mapped.write_text(mutation)
                with self.assertRaisesRegex(ValueError, 'Elligator source'):
                    gj.map_parameters(root)

    def test_actual_modular_chain_and_changed_step(self):
        d = -10240 * pow(10241, -1, gj.P) % gj.P
        half = (gj.P - 1) // 2
        steps = gj.power_steps(d, half)
        gj.validate_steps(d, half, steps)
        self.assertEqual(steps[-1][-1], gj.P - 1)
        for index in (0, len(steps) // 2, len(steps) - 1):
            changed = list(steps)
            prefix, residue, bit, following = changed[index]
            changed[index] = (prefix, residue, bit, (following + 1) % gj.P)
            with self.assertRaisesRegex(ValueError, 'modular power step'):
                gj.validate_steps(d, half, changed)
        with self.assertRaisesRegex(ValueError, 'length'):
            gj.validate_steps(d, half, steps[:-1])
        with self.assertRaises(ValueError):
            gj.validate_steps((d + 1) % gj.P, half, steps)

    def test_exact_runtime_parameter_body_and_field_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            curve = root / 'crates/crypto/circuits/src/group.rs'
            field = root / 'third_party/commonware/cryptography/src/bls12381/primitives/group.rs'
            curve.parent.mkdir(parents=True)
            field.parent.mkdir(parents=True)
            body = 'pub fn coefficient_d() -> Scalar { -Scalar::from(10240) * &Scalar::from(10241).inv() }'
            curve.write_text(body)
            field.write_text(f'/// r = 0x{gj.P:x}\npub struct Scalar(pub(crate) blst_fr);')
            d, imaginary, _ = gj.parameters(root)
            self.assertEqual(d * 10241 % gj.P, gj.P - 10240)
            self.assertEqual(imaginary * imaginary % gj.P, gj.P - 1)
            for mutation in (body.replace('10240', '10239'), body.replace('10241', '10242'), body + body):
                curve.write_text(mutation)
                with self.assertRaisesRegex(ValueError, 'coefficient_d'):
                    gj.parameters(root)
            curve.write_text(body)
            field.write_text(f'/// r = 0x{gj.P + 1:x}\npub struct Scalar(pub(crate) blst_fr);')
            with self.assertRaisesRegex(ValueError, 'field identity'):
                gj.parameters(root)


if __name__ == '__main__':
    unittest.main()
