import unittest
from pathlib import Path
import tempfile

import decaf_field_proof as proof


def extraction():
    array = "t_Array (t_u32) ((8 : t_usize))"
    body = f"Definition fq_add (out1 : {array}) (arg1 : {array}) (arg2 : {array}) : {array} :=\n"
    body += "\n".join(f"f_index ({name}) (({i} : t_usize))" for i in range(8) for name in ("arg1", "arg2"))
    body += "\n" + "\n".join(f"update_at_usize (out1) (({i} : t_usize))" for i in range(8))
    body += "\n" + "fq_addcarryx_u32 " * 8 + "fq_subborrowx_u32 " * 9 + "fq_cmovznz_u32 " * 8 + "cast.\n"
    return body


def multiplication_extraction():
    array = "t_Array (t_u32) ((8 : t_usize))"
    body = f"Definition fq_mul (out1 : {array}) (arg1 : {array}) (arg2 : {array}) : {array} :=\n"
    reads = [("arg1", i) for i in (*range(1, 8), 0)]
    reads += [("arg2", i) for _ in range(8) for i in range(7, -1, -1)]
    body += "\n".join(f"f_index ({name}) (({i} : t_usize))" for name, i in reads)
    body += "\n" + "\n".join(f"update_at_usize (out1) (({i} : t_usize))" for i in range(8))
    for name, count in {"fq_mulx_u32": 128, "fq_addcarryx_u32": 239, "fq_subborrowx_u32": 9,
                        "fq_cmovznz_u32": 8, "f_add": 23, "cast": 31}.items():
        body += "\n" + (name + " ") * count
    return body + ".\n"


class NativeFieldProofTests(unittest.TestCase):
    def test_rust_binding_requires_compiler_cargo_rustdoc_and_driver(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            (root / "lib").mkdir()
            for name in ("rustc", "cargo", "rustdoc"):
                (root / "bin" / name).write_bytes(name.encode())
            driver = root / "lib/librustc_driver-test.so"
            driver.write_bytes(b"driver")

            def command(args):
                if args[:4] == ["rustup", "which", "--toolchain", "pinned"]:
                    self.assertIn(args[-1], ("rustc", "cargo", "rustdoc"))
                    return str(root / "bin" / args[-1]) + "\n"
                self.assertEqual(args, [root / "bin/rustc", "--print", "sysroot"])
                return str(root) + "\n"

            for host, suffix in (("x86_64-unknown-linux-gnu", "so"), ("aarch64-apple-darwin", "dylib")):
                driver.unlink(missing_ok=True)
                driver = root / ("lib/librustc_driver-test." + suffix)
                driver.write_bytes(b"driver")
                with self.subTest(host=host):
                    executables, hashes, library = proof.rust_toolchain(command, "pinned", host)
                    self.assertEqual(library, root / "lib")
                    self.assertEqual(set(executables), {"rustc", "cargo", "rustdoc"})
                    self.assertEqual(set(hashes), {str(path) for path in [*executables.values(), driver]})
                    proof.validate_artifact_hashes(hashes)
                    driver.unlink()
                    with self.assertRaises(ValueError):
                        proof.rust_toolchain(command, "pinned", host)
            with self.assertRaises(ValueError):
                proof.rust_toolchain(command, "pinned", "unsupported")

    def test_execution_and_import_artifacts_must_stay_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            path = (Path(directory) / "compiler-or-proof.vo").resolve()
            path.write_bytes(b"original")
            hashes = {str(path): proof.formal.file_digest(path)}
            proof.validate_artifact_hashes(hashes)
            path.write_bytes(b"changed")
            with self.assertRaises(ValueError):
                proof.validate_artifact_hashes(hashes)
            path.unlink()
            with self.assertRaises(FileNotFoundError):
                proof.validate_artifact_hashes(hashes)
        with self.assertRaises(ValueError):
            proof.validate_artifact_hashes({})

    def test_changed_or_missing_replay_inputs_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            case = work / "original"
            paths = [case / name for name in ("Cargo.toml", "lib.rs", "fiat.rs",
                "proofs/coq/extraction/Decaf_proof_slice_Fiat.v", "support/Core.v")]
            for path in paths:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("source\n")
            cases = {"original": {
                "input_hashes": {path.name: proof.formal.file_digest(path) for path in paths[:3]},
                "extraction_sha256": proof.formal.file_digest(paths[3])}}
            hashes = {"Core": proof.formal.file_digest(paths[4])}
            proof.validate_case_files(work, cases, hashes)
            for path in paths:
                path.write_text("changed\n")
                with self.subTest(path=path), self.assertRaises(ValueError):
                    proof.validate_case_files(work, cases, hashes)
                path.write_text("source\n")
            paths[4].unlink()
            with self.assertRaises(FileNotFoundError):
                proof.validate_case_files(work, cases, hashes)

    def test_mul_access_and_operation_mutations(self):
        original = multiplication_extraction()
        proof.validate_mul_accesses(original)
        for changed in (original.replace("f_index (arg2) ((7", "f_index (arg2) ((8", 1),
                        original.replace("f_index (arg2) ((7", "f_index (arg2) ((6", 1),
                        original.replace("update_at_usize (out1) ((7", "update_at_usize (out1) ((8", 1),
                        original.replace("fq_mulx_u32", "fq_unknown", 1),
                        original.replace("f_add", "f_sub", 1),
                        original.replace("cast ", "", 1)):
            with self.subTest(changed=changed[:80]), self.assertRaises(ValueError):
                proof.validate_mul_accesses(changed)

    def test_access_schedule(self):
        proof.validate_accesses(extraction())
        for changed in (
                extraction().replace("f_index (arg1) ((7", "f_index (arg1) ((8"),
                extraction().replace("f_index (arg1) ((7", "f_index (arg1) ((6"),
                extraction().replace("update_at_usize (out1) ((7", "update_at_usize (out1) ((6"),
                extraction().replace("cast.", "cast f_sub."),
                extraction().replace("fq_cmovznz_u32", "fq_unknown", 1),
                extraction().replace("(8 : t_usize)", "(9 : t_usize)", 1),
                extraction() + "Admitted.\n"):
            with self.assertRaises(ValueError):
                proof.validate_accesses(changed)

    def test_modulus_mutation_is_confined(self):
        line = "fq_subborrowx_u32(&mut x17, &mut x18, 0x0, x1, (0x1 as u32));"
        source = line + "\npub const fn fq_add() {\n" + line + "\n}\n" + line
        self.assertEqual(proof.modulus_mutation(source).count("0x2 as"), 1)
        with self.assertRaises(ValueError):
            proof.modulus_mutation("pub const fn fq_add() {\n}\n")

    def test_multiplication_mutation_is_confined(self):
        line = "let x1: u64 = ((arg1 as u64) * (arg2 as u64));"
        source = line + "\npub const fn fq_mulx_u32() {\n" + line + "\n}\n" + line
        changed = proof.multiplication_mutation(source)
        self.assertEqual(changed.count("+ 1"), 1)
        self.assertTrue(changed.startswith(line))
        self.assertTrue(changed.endswith(line))
        with self.assertRaises(ValueError):
            proof.multiplication_mutation("pub const fn fq_mulx_u32() {\n}\n")

    def test_field_rejection_requires_arithmetic_failure(self):
        good = 'File "RustFieldAdd.v", line 10, characters 2-5:\nError: Tactic failure: Cannot find witness.\n'
        proof.validate_rejection(good)
        proof.validate_rejection(good.replace('failure: ', 'failure:  '))
        for text in (good.replace('Tactic failure: Cannot find witness.', 'Cannot infer a type'),
                     good.replace('RustFieldAdd.v', 'Core.v'),
                     good.replace('Error:', 'Warning:'),
                     'File "RustFieldAdd.v", line 1, characters 2-3:\nWarning: unused.\n' + good.replace('RustFieldAdd.v', 'Core.v'),
                     'Error: Unrelated compiler failure.\n' + good,
                     good + 'Error: Unrelated compiler failure.\n',
                     good + good):
            with self.assertRaises(ValueError):
                proof.validate_rejection(text)

    def test_rejection_exit_codes_are_tool_specific(self):
        self.assertTrue(proof.expected_failure('verification process failed (1); see proof.log', 1))
        self.assertTrue(proof.expected_failure('verification process failed (101); see cargo.log', 101))
        for code in (101, 124, 137, -9):
            self.assertFalse(proof.expected_failure(f'verification process failed ({code}); see proof.log', 1))
        self.assertFalse(proof.expected_failure('timeout: verification process failed (1); see proof.log', 1))

    def test_assumptions_must_be_exactly_closed(self):
        proof.validate_assumptions("Closed under the global context\n" * len(proof.ROOTS))
        with self.assertRaises(ValueError):
            proof.validate_assumptions("Axioms: arithmetic\n")


if __name__ == "__main__":
    unittest.main()
