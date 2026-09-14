from contextlib import nullcontext
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import formal
import decaf_go_resolver_proof as replay


class GoResolverReplayTests(unittest.TestCase):
    def test_controls_require_exact_mutation_and_error_site(self):
        for kind, name, anchor in (
            ("wrong-underlying", "underlying_FqUint1",
             "if decide (t = fiat.FqUint1) then fiat.FqUint1ⁱᵐᵖˡ else"),
            ("wrong-dispatch", "resolve_FqAdd",
             "if decide (name = fiat.FqAdd) then as_function fiat.FqAddⁱᵐᵖˡ else")):
            source = anchor + "\nLemma " + name + " : proposition.\nProof. reflexivity. Qed.\n"
            changed = replay.mutate(source, kind)
            with self.assertRaises(ValueError):
                replay.mutate(changed, kind)
            with tempfile.TemporaryDirectory() as temp:
                path = Path(temp) / "GoFieldResolver.v"
                path.write_text(changed)
                diagnostic = f'File "{path.resolve()}", line 3, characters 7-18:\nError: Unable to unify "a" with "b".'
                replay.validate_rejection(diagnostic, changed, path, kind)
                for invalid in (diagnostic.replace("line 3", "line 2"),
                                diagnostic.replace("Unable to unify", "Missing import"),
                                diagnostic + "\n" + diagnostic,
                                diagnostic.replace(str(path.resolve()), str(path.parent / "other.v"))):
                    with self.assertRaises(ValueError):
                        replay.validate_rejection(invalid, changed, path, kind)

    def test_interruption_invalidates_previous_success(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            directory = work / "decaf-go-resolver-proof"
            directory.mkdir()
            receipt = directory / "report.json"
            receipt.write_text('{"status":"passed","completed":true}')
            with patch.object(formal, "WORK", work), patch.object(formal, "exclusive_lock", return_value=nullcontext()), \
                    patch.object(replay.tempfile, "mkdtemp", side_effect=KeyboardInterrupt):
                self.assertEqual(replay.main(), 1)
            result = json.loads(receipt.read_text())
            self.assertEqual(result["status"], "failed")
            self.assertFalse(result["completed"])
            self.assertFalse(result["full_certification"])
