from __future__ import annotations

import importlib.util
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("formal_cli", ROOT / "formal.py")
assert SPEC and SPEC.loader
FORMAL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FORMAL)


class FormalCliTests(unittest.TestCase):
    def test_wslenv_replaces_flags_without_dropping_other_entries(self) -> None:
        env = {"WSLENV": "OTHER:VALUE"}
        FORMAL.expose_to_wsl(env, "VALUE", path=True)
        self.assertEqual(env["WSLENV"], "OTHER:VALUE/p")

    def test_windows_commands_export_native_python_to_wsl(self) -> None:
        if FORMAL.os.name != "nt":
            self.skipTest("Windows-only command bridge")
        env = FORMAL.command_environment()
        self.assertEqual(env["FV_WINDOWS_PYTHON"], FORMAL.sys.executable)
        self.assertIn("FV_WINDOWS_PYTHON/p", env["WSLENV"].split(":"))
        self.assertTrue(Path(env["FV_GATE_TMP_ROOT"]).is_dir())
        self.assertIn("FV_GATE_TMP_ROOT/p", env["WSLENV"].split(":"))
        self.assertEqual(env["FV_GATE_TEST_SCOPE"], "full")
        self.assertIn("FV_GATE_TEST_SCOPE", env["WSLENV"].split(":"))

    def test_windows_gate_catalog_is_generated_natively_once(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            env: dict[str, str] = {}
            with (
                patch.object(FORMAL.os, "name", "nt"),
                patch.object(FORMAL, "run", return_value="profile\ttransfer") as run,
            ):
                FORMAL.prepare_windows_gate_catalog(checkout, env)

            run.assert_called_once_with(
                [
                    FORMAL.sys.executable,
                    str(checkout / "scripts/check-fv-profiles.py"),
                    "--emit-gate-catalog-tsv",
                    "--status",
                    "certified",
                ],
                cwd=checkout,
                capture=True,
            )
            self.assertEqual(
                (checkout / ".formal-gate-catalog.tsv").read_bytes(),
                b"profile\ttransfer\n",
            )
            self.assertEqual(env["FV_GATE_CATALOG_FILE"], ".formal-gate-catalog.tsv")
            self.assertIn("FV_GATE_CATALOG_FILE", env["WSLENV"].split(":"))

    def test_refresh_validation_uses_focused_generator_tests(self) -> None:
        env: dict[str, str] = {}
        with patch.object(FORMAL.os, "name", "nt"):
            FORMAL.use_refresh_validation_scope(env)

        self.assertEqual(env["FV_GATE_TEST_SCOPE"], "refresh")
        self.assertIn("FV_GATE_TEST_SCOPE", env["WSLENV"].split(":"))

        source = (ROOT / "scripts/check-lean-circuit-fv.sh").read_text()
        self.assertIn('gate_test_scope="${FV_GATE_TEST_SCOPE:-full}"', source)
        self.assertIn("python3 -m unittest test_generator_mtime.py", source)
        self.assertIn("python3 -m unittest discover -p 'test_*.py'", source)
        self.assertIn(
            'check-formal-gate-self-tests.sh" "$gate_test_scope"', source
        )

    def test_refresh_pins_complete_semantic_bundle_before_certification(self) -> None:
        source = (ROOT / "scripts/refresh-formal-evidence.sh").read_text()
        ownership = source.index("gen_template_ownership.py")
        semantic_pin = source.index("--emit-semantic-digest")
        certification = source.index("gen-certified-circuit-artifacts.py")

        self.assertLess(ownership, semantic_pin)
        self.assertLess(semantic_pin, certification)
        self.assertIn("certified-protocol-semantics.sha256", source)

    def test_parser_requires_exact_gate_kind(self) -> None:
        args = FORMAL.parser().parse_args(["gate", "soundness", "--mode", "drift"])
        self.assertEqual((args.gate, args.mode), ("soundness", "drift"))

    def test_refresh_requires_explicit_all_scope(self) -> None:
        with self.assertRaises(SystemExit):
            FORMAL.parser().parse_args(["evidence", "refresh"])
        args = FORMAL.parser().parse_args(["evidence", "refresh", "--all"])
        self.assertTrue(args.all)

    def test_snapshot_ignores_compiler_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "proof").mkdir()
            (root / "proof" / "A.lean").write_text("theorem a : True := by trivial\n")
            (root / "proof" / ".lake").mkdir()
            (root / "proof" / ".lake" / "A.olean").write_bytes(b"cache")
            snapshot = FORMAL.snapshot(root, ["proof"])
        self.assertEqual(list(snapshot), ["proof/A.lean"])

    def test_declared_lfs_inputs_are_narrow_runtime_artifacts(self) -> None:
        ownership = FORMAL.read_json(ROOT / "formal-files.json")
        self.assertEqual(len(ownership["lfs_inputs"]), 4)
        self.assertTrue(
            all(path.endswith(".sr1cs") for path in ownership["lfs_inputs"])
        )
        self.assertEqual(ownership["merge_paths"], ["scripts"])

    def test_lfs_content_must_match_locked_pointer(self) -> None:
        payload = b"certified constraints"
        oid = hashlib.sha256(payload).hexdigest()
        pointer = (
            "version https://git-lfs.github.com/spec/v1\n"
            f"oid sha256:{oid}\n"
            f"size {len(payload)}\n"
        )
        self.assertEqual(
            FORMAL.parse_lfs_pointer(pointer, "artifact.sr1cs"),
            (oid, len(payload)),
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "artifact.sr1cs"
            path.write_bytes(payload)
            FORMAL.verify_lfs_content(path, "artifact.sr1cs", oid, len(payload))
            path.write_bytes(b"wrong constraints")
            with self.assertRaises(FORMAL.FormalError):
                FORMAL.verify_lfs_content(path, "artifact.sr1cs", oid, len(payload))

    def test_materialized_lfs_copy_is_reused_only_after_digest_validation(self) -> None:
        payload = b"certified constraints"
        oid = hashlib.sha256(payload).hexdigest()
        pointer = (
            "version https://git-lfs.github.com/spec/v1\n"
            f"oid sha256:{oid}\n"
            f"size {len(payload)}\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            checkout = root / "checkout"
            source.mkdir()
            checkout.mkdir()
            (source / "artifact.sr1cs").write_bytes(payload)
            (checkout / "artifact.sr1cs").write_text(pointer, encoding="ascii")
            FORMAL.run(["git", "init"], cwd=checkout)
            FORMAL.run(["git", "config", "user.email", "formal@example.invalid"], cwd=checkout)
            FORMAL.run(["git", "config", "user.name", "Formal Test"], cwd=checkout)
            FORMAL.run(["git", "add", "artifact.sr1cs"], cwd=checkout)
            FORMAL.run(["git", "commit", "-m", "pointer"], cwd=checkout)
            sha = FORMAL.run(["git", "rev-parse", "HEAD"], cwd=checkout, capture=True)
            ownership = root / "formal-files.json"
            ownership.write_text(
                json.dumps({"lfs_inputs": ["artifact.sr1cs"]}), encoding="utf-8"
            )

            with patch.object(FORMAL, "OWNERSHIP_PATH", ownership):
                FORMAL.materialize_lfs(str(source), checkout, sha)
                (source / "artifact.sr1cs").write_bytes(b"invalid source data")
                FORMAL.materialize_lfs(str(source), checkout, sha)

            self.assertEqual((checkout / "artifact.sr1cs").read_bytes(), payload)

    def test_sync_path_updates_and_removes_without_hardlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            destination = root / "destination"
            source.mkdir()
            destination.mkdir()
            (source / "kept.txt").write_text("new value", encoding="utf-8")
            (destination / "kept.txt").write_text("old", encoding="utf-8")
            (destination / "stale.txt").write_text("stale", encoding="utf-8")
            FORMAL.sync_path(source, destination)
            self.assertEqual(
                (destination / "kept.txt").read_text(encoding="utf-8"), "new value"
            )
            self.assertFalse((destination / "stale.txt").exists())
            self.assertNotEqual(
                (source / "kept.txt").stat().st_ino,
                (destination / "kept.txt").stat().st_ino,
            )

    def test_merge_path_preserves_shieldd_owned_files_and_removes_stale_overlay(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout = root / "checkout"
            overlay = root / "overlay" / "scripts"
            checkout.mkdir()
            overlay.mkdir(parents=True)
            FORMAL.run(["git", "init"], cwd=checkout)
            FORMAL.run(["git", "config", "user.email", "formal@example.invalid"], cwd=checkout)
            FORMAL.run(["git", "config", "user.name", "Formal Test"], cwd=checkout)
            (checkout / "scripts").mkdir()
            (checkout / "scripts" / "runtime.py").write_text("runtime\n", encoding="utf-8")
            FORMAL.run(["git", "add", "scripts/runtime.py"], cwd=checkout)
            FORMAL.run(["git", "commit", "-m", "runtime"], cwd=checkout)
            sha = FORMAL.run(["git", "rev-parse", "HEAD"], cwd=checkout, capture=True)
            (checkout / "scripts" / "stale.py").write_text("stale\n", encoding="utf-8")
            (overlay / "formal.py").write_text("formal\n", encoding="utf-8")

            FORMAL.merge_path(overlay, checkout / "scripts", checkout, "scripts", sha)

            self.assertEqual(
                (checkout / "scripts" / "runtime.py").read_text(encoding="utf-8"),
                "runtime\n",
            )
            self.assertEqual(
                (checkout / "scripts" / "formal.py").read_text(encoding="utf-8"),
                "formal\n",
            )
            self.assertFalse((checkout / "scripts" / "stale.py").exists())

    def test_orphan_run_cleanup_removes_stale_registered_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            work = root / "work"
            runs = work / "runs"
            active = runs / "active"
            orphan = runs / "orphan"
            active.mkdir(parents=True)
            orphan.mkdir()
            (orphan / "partial.txt").write_text("partial", encoding="utf-8")

            def fake_run(args, **_kwargs):
                if "list" in args:
                    return f"worktree {active.resolve()}\n"
                return ""

            with (
                patch.object(FORMAL, "WORK", work),
                patch.object(FORMAL, "run", side_effect=fake_run),
                patch.object(FORMAL, "remove_registered_worktree") as remove,
            ):
                FORMAL.remove_orphan_runs(root / "mirror.git")

            remove.assert_called_once_with(root / "mirror.git", active.resolve())
            self.assertFalse(orphan.exists())

    def test_promotion_rolls_back_all_applied_files_on_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "formal"
            checkout = Path(directory) / "checkout"
            for base in (root, checkout):
                (base / "evidence").mkdir(parents=True)
            (root / "evidence/a.txt").write_text("old a", encoding="utf-8")
            (root / "evidence/b.txt").write_text("old b", encoding="utf-8")
            (checkout / "evidence/a.txt").write_text("new a", encoding="utf-8")
            (checkout / "evidence/b.txt").write_text("new b", encoding="utf-8")
            before = FORMAL.snapshot(root, ["evidence"])
            after = FORMAL.snapshot(checkout, ["evidence"])
            original_replace = FORMAL.os.replace
            failed = False

            def fail_second(source: Path, destination: Path) -> None:
                nonlocal failed
                source_path = Path(source)
                destination_path = Path(destination)
                if (
                    not failed
                    and destination_path == root / "evidence/b.txt"
                    and "staged" in source_path.parts
                ):
                    failed = True
                    raise OSError("injected promotion failure")
                original_replace(source, destination)

            old_root = FORMAL.ROOT
            FORMAL.ROOT = root
            try:
                with patch.object(FORMAL.os, "replace", side_effect=fail_second):
                    with self.assertRaises(OSError):
                        FORMAL.promote(checkout, before, after)
            finally:
                FORMAL.ROOT = old_root

            self.assertEqual(
                (root / "evidence/a.txt").read_text(encoding="utf-8"), "old a"
            )
            self.assertEqual(
                (root / "evidence/b.txt").read_text(encoding="utf-8"), "old b"
            )


if __name__ == "__main__":
    unittest.main()
