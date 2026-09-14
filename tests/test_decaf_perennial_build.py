import json
import tempfile
import unittest
import copy
from pathlib import Path
from unittest.mock import patch
from contextlib import nullcontext

import formal
import decaf_perennial_build as build


class PerennialBuildTests(unittest.TestCase):
    def test_exported_source_mutations_and_additions_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            path = root / "Semantics.v"
            path.write_text("Definition x := 1.")
            report = {"source_root": str(root), "source_files": {path.name: formal.file_digest(path)}, "source_links": {}}
            build.validate_sources(report)
            extra = root / "Extra.v"
            extra.write_text("Definition y := 2.")
            with self.assertRaises(ValueError):
                build.validate_sources(report)
            extra.unlink()
            path.write_text("Definition x := 2.")
            with self.assertRaises(ValueError):
                build.validate_sources(report)
            path.unlink()
            with self.assertRaises(ValueError):
                build.validate_sources(report)

    def test_missing_target_and_changed_artifact_inventory_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "source"
            root.mkdir()
            library = Path(temp) / "lib"
            library.mkdir()
            (library / "Import.vo").write_bytes(b"fixture external import")
            source_files = {}
            for name in build.TARGETS:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"fixture artifact, not a compiled proof")
                source = path.with_suffix(".v")
                source.write_text("Definition fixture := 1.")
                source_files[str(source.relative_to(root))] = formal.file_digest(source)
            for name in ("Makefile", "_RocqProject"):
                (root / name).write_text("fixture")
                source_files[name] = formal.file_digest(root / name)
            report = {"status": "passed", "completed": True, "full_certification": False,
                      "targets": list(build.TARGETS), "revision": "revision", "patch_sha256": "patch",
                      "source_root": str(root), "source_files": source_files, "source_links": {},
                      "artifacts": build.hashes(root, lambda path: path.suffix in build.COMPILED),
                      "library_root": str(library), "installed_imports": build.installed_hashes(library),
                      "sources": [{"revision": "revision", "destination": str(root)}],
                      "input_hashes": {"input": "hash"}, "tools": {"tool": "hash"}}
            config = {"perennial": {"revision": "revision", "patch_sha256": "patch"}}
            # Concrete artifact hashes; tool/input resolution is isolated from the host.
            with patch.object(build, "input_hashes", return_value=report["input_hashes"]), \
                    patch.object(build, "tool_hashes", return_value=report["tools"]):
                original_digest = formal.file_digest
                def digest(path):
                    return "hash" if str(path) in ("input", "tool") else original_digest(path)
                with patch.object(formal, "file_digest", side_effect=digest):
                    build.validate_build(report, config)
                    for key in ("input_hashes", "tools", "sources", "source_files", "installed_imports"):
                        mutant = copy.deepcopy(report)
                        mutant[key] = [] if key == "sources" else {}
                        with self.assertRaises(ValueError):
                            build.validate_build(mutant, config)
                    extra = root / "Stale.vo"
                    extra.write_bytes(b"stale")
                    with self.assertRaises(ValueError):
                        build.validate_build(report, config)
                    extra.unlink()
                    (root / build.TARGETS[0]).unlink()
                    with self.assertRaises(ValueError):
                        build.validate_build(report, config)

    def test_early_failure_invalidates_old_success(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            directory = work / "decaf-perennial-build"
            directory.mkdir()
            path = directory / "report.json"
            path.write_text('{"status":"passed","completed":true}')
            with patch.object(formal, "WORK", work), patch.object(formal, "exclusive_lock", return_value=nullcontext()), \
                    patch.object(formal, "file_digest", side_effect=KeyboardInterrupt), patch("sys.argv", ["build"]):
                self.assertEqual(build.main(), 1)
            report = json.loads(path.read_text())
            self.assertEqual(report["status"], "failed")
            self.assertFalse(report["completed"])
