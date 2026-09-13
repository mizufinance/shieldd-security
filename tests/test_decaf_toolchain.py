import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from decaf_toolchain import native_artifact, native_host


class NativeToolchainTests(unittest.TestCase):
    def setUp(self):
        self.config = json.loads((Path(__file__).resolve().parents[1] /
                                  "decaf/proofs/toolchain.json").read_text())

    def test_mac_pins_preserved(self):
        with patch("decaf_toolchain.native_host", return_value="aarch64-apple-darwin"):
            self.assertEqual(native_artifact(self.config, "fiat")["binary_sha256"],
                             self.config["fiat"]["native_build"]["binary_sha256"])
            self.assertEqual(native_artifact(self.config, "hax")["binary_sha256"],
                             self.config["hax"]["binary_sha256"])
            self.assertEqual(native_artifact(self.config, "goose")["binary_sha256"],
                             self.config["perennial"]["goose_sha256"])

    def test_unregistered_host_cannot_use_mac_hashes(self):
        config = copy.deepcopy(self.config)
        config.pop("native_builds", None)
        with patch("decaf_toolchain.native_host", return_value="x86_64-unknown-linux-gnu"):
            for tool in ("fiat", "hax", "goose"):
                with self.assertRaisesRegex(ValueError, "no reviewed"):
                    native_artifact(config, tool)

    def test_host_entry_does_not_authorize_other_tools(self):
        config = copy.deepcopy(self.config)
        config["native_builds"] = {"x86_64-unknown-linux-gnu": {
            "goose": {"binary_sha256": "a" * 64}}}
        with patch("decaf_toolchain.native_host", return_value="x86_64-unknown-linux-gnu"):
            self.assertEqual(native_artifact(config, "goose")["binary_sha256"], "a" * 64)
            with self.assertRaisesRegex(ValueError, "no reviewed"):
                native_artifact(config, "hax")
            config["native_builds"]["x86_64-unknown-linux-gnu"]["goose"]["binary_sha256"] = ""
            with self.assertRaisesRegex(ValueError, "invalid"):
                native_artifact(config, "goose")

    def test_unknown_architecture_fails_closed(self):
        with patch("decaf_toolchain.platform.system", return_value="Linux"), \
                patch("decaf_toolchain.platform.machine", return_value="aarch64"):
            with self.assertRaisesRegex(ValueError, "unsupported"):
                native_host()

    def test_explicit_hax_identity_must_cover_every_executable(self):
        config = copy.deepcopy(self.config)
        config["native_builds"] = {"x86_64-unknown-linux-gnu": {
            "hax": {"binary_sha256": {"cargo-hax": "a" * 64}}}}
        with patch("decaf_toolchain.native_host", return_value="x86_64-unknown-linux-gnu"):
            with self.assertRaisesRegex(ValueError, "incomplete"):
                native_artifact(config, "hax")
