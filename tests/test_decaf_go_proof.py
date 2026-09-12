import unittest
import tempfile
from pathlib import Path

import decaf_go_proof as proof


class GoCarryProofTests(unittest.TestCase):
    def test_isolated_toolchain_preserves_original_sources(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            (source / "src/math/bits").mkdir(parents=True)
            (source / "bin").mkdir()
            (source / "src/runtime").mkdir()
            original = source / "src/math/bits/bits.go"
            original.write_text("original")
            original.chmod(0o444)
            isolated = root / "isolated"
            proof.copy_bits_goroot(source, isolated)
            changed = isolated / "src/math/bits/bits.go"
            changed.write_text("mutant")
            self.assertEqual(original.read_text(), "original")
            self.assertFalse(changed.is_symlink())
            self.assertFalse((isolated / "src").is_symlink())
            self.assertTrue((isolated / "src/runtime").is_symlink())

    def test_mutation_is_confined_to_add64(self):
        source = "func Other() { x >>= 63 }\nfunc Add64(x uint64) uint64 {\nreturn x >> 63\n}\nfunc Last() { x >>= 63 }\n"
        mutated = proof.shift_mutation(source)
        self.assertEqual(mutated, source.replace("return x >> 63", "return x >> 62"))

    def test_borrow_mutation_is_confined_to_sub64(self):
        source = "func Add64() { return x >> 63 }\nfunc Sub64() {\nreturn x >> 63\n}\n"
        mutated = proof.shift_mutation(source, "Sub64")
        self.assertEqual(mutated, source.replace("\nreturn x >> 63", "\nreturn x >> 62"))
        with self.assertRaises(ValueError):
            proof.shift_mutation(source, "Other")

    def test_borrow_rejection_requires_its_execution_theorem(self):
        proof.validate_rejection('File "GoBorrow.v":\nError: (in proof subborrow_execution): Attempt to save an incomplete proof', "GoBorrow")
        for text in ('File "GoCarry.v":\nError: Tactic failure',
                     'File "GoBorrow.v":\nError: Cannot find a physical path',
                     'File "GoBorrow.v":\nError: (in proof other): Attempt to save an incomplete proof'):
            with self.assertRaises(ValueError):
                proof.validate_rejection(text, "GoBorrow")

    def test_mutation_rejects_missing_or_ambiguous_shift(self):
        for body in ("return x", "return x >> 63 >> 63"):
            with self.assertRaises(ValueError):
                proof.shift_mutation("func Add64(x uint64) uint64 {\n" + body + "\n}")

    def test_closed_audit_accepts_exact_roots_only(self):
        closed = "Closed under the global context\n"
        proof.validate_assumptions(closed * len(proof.ROOTS))
        for text in (closed, closed * 4, closed * 3 + "Axioms: unsafe\n"):
            with self.assertRaises(ValueError):
                proof.validate_assumptions(text)

    def test_mutation_rejects_infrastructure_failures(self):
        proof.validate_rejection('File "GoCarry.v":\nError:  (in proof addcarry_execution): Attempt to save an incomplete proof')
        for text in ('File "GoCarry.v":\nError: Tactic failure: iApply failed',
                     'File "GoCarry.v":\nError: Cannot find a physical path',
                     'File "bits.v":\nError: Tactic failure: wrong model',
                     'killed', ''):
            with self.assertRaises(ValueError):
                proof.validate_rejection(text)


if __name__ == "__main__":
    unittest.main()
