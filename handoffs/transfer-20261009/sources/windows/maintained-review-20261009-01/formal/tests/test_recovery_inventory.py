import csv
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location(
    "recovery_inventory", Path(__file__).parents[1] / "reference/inventory.py")
inventory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inventory)


class RecoveryInventoryTests(unittest.TestCase):
    def test_reviewed_disposition_survives_regeneration_and_source_drift_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = [("protocol/model.spthy", "original/model.spthy", b"lemma secrecy: true\n")]
            with patch.object(inventory, "ROOT", root), \
                    patch.object(inventory, "source_paths", return_value=iter(sources)), \
                    patch.object(inventory, "scope_members", return_value=[]):
                output, _ = inventory.render()
            rows = list(csv.DictReader(io.StringIO(output), delimiter="\t"))
            rows[0].update(owner="protocol", migration_target="Current authenticated release",
                           disposition="retain-and-migrate", reason="Current adversary model required")
            with (root / "migration.tsv").open("w", encoding="utf-8", newline="") as handle:
                writer = csv.DictWriter(handle, rows[0], delimiter="\t", lineterminator="\n")
                writer.writeheader()
                writer.writerows(rows)
            with patch.object(inventory, "ROOT", root), \
                    patch.object(inventory, "source_paths", side_effect=lambda: iter(sources)), \
                    patch.object(inventory, "scope_members", return_value=[]):
                updated, _ = inventory.render()
                self.assertEqual(updated, (root / "migration.tsv").read_text())
                sources[0] = (sources[0][0], sources[0][1], b"lemma secrecy: false\n")
                with self.assertRaisesRegex(AssertionError, "Source changed"):
                    inventory.render()

    def test_unclassified_historical_source_fails_scope_closure(self):
        with patch.object(inventory.subprocess, "check_output", return_value="new-protocol/release.spthy\n"):
            with self.assertRaisesRegex(AssertionError, "Unaccounted historical source"):
                inventory.scope_members(set())


if __name__ == "__main__":
    unittest.main()
