import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import decaf_inventory as inventory


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.matrix = json.loads(inventory.MATRIX.read_text())

    def test_expansion_keeps_both_architectures_and_unresolved_consumers(self):
        rows = inventory.expand(self.matrix)
        self.assertEqual({row["target"] for row in rows}, inventory.TARGETS)
        self.assertEqual({row["profile"] for row in rows}, inventory.PROFILES)
        self.assertTrue(all(row["status"] == "blocked" and not row["evidence"] for row in rows))
        self.assertTrue(any(row["field"] == "fr" and row["property"] == "mul" for row in rows))
        self.assertIsNone(self.matrix["profiles"]["orbis-consumer"]["features"])
        self.assertFalse(self.matrix["profiles"]["rust-minimal"]["default_features"])
        trace = next(row for row in rows if row["family"] == "compiled-traces")
        self.assertIn("compiler", trace["transitive_assumptions"])
        self.assertNotIn("compiler", trace["direct_assumptions"])

    def test_missing_scope_and_fake_completion_are_rejected(self):
        mutations = [lambda m: m["targets"].pop(),
                     lambda m: m["profiles"].pop("rust-default"),
                     lambda m: m["sources"].pop("rdsa"),
                     lambda m: m["families"].pop(),
                     lambda m: m["families"][3].pop("fields"),
                     lambda m: m["families"][3]["properties"].remove("mul"),
                     lambda m: m["profiles"]["rust-default"].update(source="go"),
                     lambda m: m["contracts"].pop(),
                     lambda m: m["assumptions"].pop("analysis"),
                     lambda m: m["profiles"]["rust-minimal"].update(default_features=True),
                     lambda m: m.update(closure="complete"),
                     lambda m: m["sources"]["rust"].update(revision="main"),
                     lambda m: m["replays"]["rust-carry"].update(runner="../arbitrary.py")]
        for mutate in mutations:
            matrix = copy.deepcopy(self.matrix)
            mutate(matrix)
            with self.assertRaises(ValueError):
                inventory.expand(matrix)

    def test_cycles_unknown_dependencies_and_duplicate_properties_rejected(self):
        for dependencies in (["release"], ["missing"]):
            matrix = copy.deepcopy(self.matrix)
            matrix["families"][0]["depends_on"] = dependencies
            with self.assertRaises(ValueError):
                inventory.validate(matrix)
        self.matrix["families"][0]["properties"] *= 2
        with self.assertRaises(ValueError):
            inventory.validate(self.matrix)

    def test_inspection_reads_commit_not_dirty_checkout(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)

            def git(*args):
                return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.DEVNULL).decode().strip()

            git("init")
            (root / "Cargo.toml").write_text('[package]\nname="original"\n')
            git("add", "Cargo.toml")
            git("-c", "user.name=Inventory Test", "-c", "user.email=test@example.invalid", "commit", "-m", "fixture")
            revision = git("rev-parse", "HEAD")
            expected = git("rev-parse", "HEAD:Cargo.toml")
            (root / "Cargo.toml").write_text("dirty replacement")
            result = inventory.inspect_source({"revision": revision}, root, False)
            self.assertEqual(result["manifests"][0]["git_object"], expected)
            self.assertFalse(result["resolved_build_closure"])
            git("add", "Cargo.toml")
            git("-c", "user.name=Inventory Test", "-c", "user.email=test@example.invalid", "commit", "-m", "replacement")
            replacement = git("rev-parse", "HEAD")
            git("replace", revision, replacement)
            replaced = inventory.inspect_source({"revision": revision}, root, False)
            self.assertEqual(replaced["manifests"][0]["git_object"], expected)
            with self.assertRaises(ValueError):
                inventory.inspect_source({"revision": "0" * 40}, root, False)

    def test_atomic_report_replaces_previous_failure_without_temp_leftovers(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "report.json"
            inventory.atomic_json(path, {"status": "blocked", "full_certification": False})
            inventory.atomic_json(path, {"status": "blocked", "completed": False})
            self.assertEqual(json.loads(path.read_text()), {"status": "blocked", "completed": False})
            self.assertEqual(list(path.parent.iterdir()), [path])

    def test_workspace_target_aliases_and_lock_identity_remain_distinct(self):
        declaration = '''[workspace.dependencies]
decaf377 = { git = "https://example.invalid/decaf", branch = "main" }
[target.'cfg(unix)'.dependencies]
renamed = { package = "decaf377-rdsa", version = "0.11" }
'''
        records = inventory.dependency_records("Cargo.toml", declaration)
        self.assertEqual(len(records), 2)
        self.assertEqual(records[0]["declaration"]["branch"], "main")
        self.assertEqual(records[1]["package"], "decaf377-rdsa")
        locked = inventory.dependency_records("Cargo.lock", '''[[package]]
name = "decaf377"
version = "0.10.1"
source = "registry+https://example.invalid/index"
checksum = "example"
''')
        self.assertEqual(locked[0]["kind"], "cargo-lock")
        self.assertEqual(locked[0]["package"]["checksum"], "example")
