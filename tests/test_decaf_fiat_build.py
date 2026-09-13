import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from decaf_fiat_build import build_environment, export_tree, initialize_source_index


class FiatSourceBuildTests(unittest.TestCase):
    def test_build_environment_drops_compiler_and_make_overrides(self):
        overrides = {name: "injected" for name in ("COQC", "COQBIN", "COQFLAGS", "ROCQFLAGS",
                      "MAKEFLAGS", "MAKEFILES", "OCAMLPATH", "COQPATH", "BASH_ENV", "LD_PRELOAD")}
        with patch.dict(os.environ, overrides):
            clean = build_environment()
        for name in overrides:
            self.assertNotEqual(clean.get(name), "injected", name)

    def test_exact_export_preserves_executable_mode_and_ignores_dirty_source(self):
        if os.name == "nt":
            self.skipTest("Linux source-build contract")
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            repository, output = base / "repo", base / "output"
            repository.mkdir()
            output.mkdir()
            env = build_environment()
            def git(*args):
                return subprocess.check_output(["git", "-C", str(repository), *args], env=env, text=True).strip()
            git("init", "-q")
            script = repository / "compile.sh"
            script.write_text("#!/bin/sh\nexit 0\n")
            script.chmod(0o755)
            (repository / "index").symlink_to("compile.sh")
            git("add", "compile.sh", "index")
            git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "source")
            revision = git("rev-parse", "HEAD")
            script.write_text("dirty source")
            records = []
            export_tree(repository, revision, output, env, records)
            self.assertEqual((output / "compile.sh").read_text(), "#!/bin/sh\nexit 0\n")
            self.assertTrue(os.access(output / "compile.sh", os.X_OK))
            self.assertTrue((output / "index").is_symlink())
            self.assertEqual(records[0]["revision"], revision)
            (output / ".gitignore").write_text("compile.sh\n")
            initialize_source_index(output, env)
            indexed = subprocess.check_output(["git", "-C", str(output), "ls-files"], env=env, text=True)
            self.assertEqual(indexed.splitlines(), [".gitignore", "compile.sh", "index"])
            self.assertEqual((output / "compile.sh").read_text(), "#!/bin/sh\nexit 0\n")

    def test_patch_application_isolated_from_parent_git_repository(self):
        with tempfile.TemporaryDirectory() as temporary:
            outer = Path(temporary)
            subprocess.run(["git", "init", "-q", str(outer)], check=True)
            source = outer / "nested" / "source"
            source.mkdir(parents=True)
            (source / "input").write_text("old\n")
            patch_path = outer / "change.patch"
            patch_path.write_text("diff --git a/input b/input\n--- a/input\n+++ b/input\n@@ -1 +1 @@\n-old\n+new\n")
            env = dict(build_environment(), GIT_CEILING_DIRECTORIES=str(source.parent))
            subprocess.run(["git", "apply", str(patch_path)], cwd=source, env=env, check=True)
            self.assertEqual((source / "input").read_text(), "new\n")


if __name__ == "__main__":
    unittest.main()
