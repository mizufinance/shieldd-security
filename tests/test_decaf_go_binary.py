import copy
import unittest
from unittest.mock import patch

import decaf
import decaf_go_binary as binary


class GoBinaryTests(unittest.TestCase):
    def receipt(self):
        return dict(status="passed", completed=True,
                    cases=[dict(id=name, status="passed") for name in sorted(binary.EXPECTED_CONTROLS)],
                    experiment_sha256="hash", classifier_sha256="hash", process_runner_sha256="hash",
                    source_sha256="hash", patch_sha256="hash",
                    tools={"demand": dict(path="/qualified/binsec", sha256="hash",
                           solver=dict(path="/qualified/z3", sha256="hash"),
                           components={"/qualified/plugin": "hash"})})

    def test_stale_incomplete_or_changed_tool_evidence_blocks(self):
        changes = [lambda r: r.update(completed=False), lambda r: r["cases"].pop(),
                   lambda r: r["cases"][0].update(status="blocked"),
                   lambda r: r["cases"][0].update(id="1"),
                   lambda r: r["tools"]["demand"].update(components={}),
                   lambda r: r.update(classifier_sha256="stale"),
                   lambda r: r["tools"]["demand"].update(sha256="stale"),
                   lambda r: r["tools"]["demand"]["components"].update({"/qualified/plugin": "stale"})]
        with patch.object(binary.formal, "file_digest", return_value="hash"), \
                patch.object(binary, "component_paths", return_value={"/qualified/plugin"}), \
                patch.object(binary.shutil, "which", side_effect=lambda name: "/qualified/" + name):
            binary.validate_qualification(self.receipt())
            for change in changes:
                receipt = copy.deepcopy(self.receipt())
                change(receipt)
                with self.assertRaises(decaf.Blocked):
                    binary.validate_qualification(receipt)

    def test_wrong_selected_binary_blocks(self):
        with patch.object(binary.formal, "file_digest", return_value="hash"), \
                patch.object(binary, "component_paths", return_value={"/qualified/plugin"}), \
                patch.object(binary.shutil, "which", return_value="/other/binsec"):
            with self.assertRaises(decaf.Blocked):
                binary.validate_qualification(self.receipt())

    def test_unknown_runtime_profile_blocks_before_snapshot(self):
        with self.assertRaises(decaf.Blocked):
            decaf.Pilot.analyze(None, None, None, language="go", runtime_profile="unrecorded")

    def test_version_probe_uses_the_declared_build_environment(self):
        pilot = object.__new__(decaf.Pilot)
        pilot.env = {"PATH": "/qualified", "GOTOOLCHAIN": "go1.25.4"}
        pilot.report = {}
        with patch.object(decaf.shutil, "which", return_value="/qualified/go") as which, \
                patch.object(decaf.subprocess, "check_output", return_value="go version go1.25.4 linux/amd64\n") as run:
            pilot.tool("go", "1.25.4")
            which.assert_called_once_with("go", path="/qualified")
            run.assert_called_once_with(["go", "version"], text=True, env=pilot.env)


if __name__ == "__main__":
    unittest.main()
