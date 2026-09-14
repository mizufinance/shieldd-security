import hashlib
from pathlib import Path
import re
import tempfile
import unittest
import os
import sys
from unittest.mock import patch

import decaf_go_execution as execution
import decaf_go_resolver_proof as replay
import formal


class GoExecutionTests(unittest.TestCase):
    @unittest.skipUnless(os.name == "posix", "runner requires POSIX process groups")
    def test_process_budget_failures_are_not_proof_rejections(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            log = root / "command.log"
            def run(code, timeout=10):
                return replay.bounded_proof_run([sys.executable, "-c", code], root,
                                                dict(os.environ), log, timeout)
            run("print('closed')")
            self.assertEqual(log.read_text().strip(), "closed")
            with self.assertRaisesRegex(RuntimeError, r"verification process failed \(1\)"):
                run("raise SystemExit(1)")
            with patch.object(replay, "LOG_BYTES", 64):
                with self.assertRaisesRegex(RuntimeError, "command output exceeded"):
                    run("print('x'*128); raise SystemExit(1)")
            log.unlink()
            with patch.object(replay, "PROOF_BYTES", 64):
                with self.assertRaisesRegex(RuntimeError, "proof artifacts exceeded"):
                    run("from pathlib import Path; Path('object.vo').write_bytes(b'x'*128)")
            (root / "object.vo").unlink()
            with self.assertRaisesRegex(RuntimeError, "wall-clock budget"):
                run("import time; time.sleep(30)", timeout=0.05)
            with self.assertRaisesRegex(RuntimeError, "wall-clock budget"):
                run("import time; time.sleep(0.15); raise SystemExit(1)", timeout=0.05)

    def test_roots_and_source_inventory(self):
        self.assertEqual(len(replay.ROOTS), 317)
        self.assertEqual(len(set(replay.ROOTS)), len(replay.ROOTS))
        for module in execution.MODULES:
            self.assertTrue((formal.ROOT / "decaf/proofs/rocq" / (module + ".v")).is_file())
        self.assertNotIn("GoFieldMulProgress", execution.MODULES)

    def test_shape_inventory_binds_both_inputs(self):
        source = execution.render_shapes(b"field", b"bits")
        self.assertEqual(len(re.findall(r"^Lemma shape_", source, re.M)), 35)
        for data in (b"field", b"bits"):
            self.assertIn(hashlib.sha256(data).hexdigest(), source)
        self.assertNotEqual(source, execution.render_shapes(b"changed", b"bits"))
        self.assertNotEqual(source, execution.render_shapes(b"field", b"changed"))
        with self.assertRaises(TypeError):
            execution.render_shapes("field", b"bits")

    def test_controls_bind_real_sources_and_exact_proof_sites(self):
        proofs = formal.ROOT / "decaf/proofs/rocq"
        for kind, (changed_module, rejected_module, theorem) in execution.CONTROLS.items():
            original = (proofs / (changed_module + ".v")).read_text(encoding="utf-8")
            changed = replay.mutate(original, kind)
            self.assertNotEqual(original, changed)
            for bad in (changed, original + original, ""):
                with self.assertRaises(ValueError):
                    replay.mutate(bad, kind)
            source = changed if changed_module == rejected_module else (proofs / (rejected_module + ".v")).read_text(encoding="utf-8")
            start = source.index("Lemma " + theorem)
            site = source.index("reflexivity.", start)
            line = source.count("\n", 0, site) + 1
            with tempfile.TemporaryDirectory() as temp:
                path = Path(temp) / (rejected_module + ".v")
                path.write_text(source, encoding="utf-8")
                error = f'File "{path.resolve()}", line {line}, characters 7-18:\nError: Unable to unify "a" with "b".'
                replay.validate_rejection(error, source, path, kind)
                for bad in (error.replace(f"line {line}", f"line {line+1}"), error + "\n" + error,
                            error.replace("Unable to unify", "Missing library")):
                    with self.assertRaises(ValueError):
                        replay.validate_rejection(bad, source, path, kind)


if __name__ == "__main__":
    unittest.main()
