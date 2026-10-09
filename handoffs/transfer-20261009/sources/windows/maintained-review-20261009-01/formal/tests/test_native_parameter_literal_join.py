"""Finite source-data controls, with no captured runtime or kernel credit."""
import copy
import json
from pathlib import Path
import re
import tempfile
import unittest

from circuits.generate_native_parameter_literal_join import SourceParser, checked, generate
from circuits.generate_native_poseidon_parameters import _table
from circuits.poseidon_graph import P


def fixture(directory):
    records, canonical = [], ""
    for file, label, width in (("poseidon381.json", "small", 3),
                               ("poseidon381-wide.json", "wide", 6)):
        matrices = {kind: [[1 + r * width + c for c in range(width)]
                           for r in range(height)] for kind, height in (("ark", 65), ("mds", width))}
        obj = dict(schema="shieldd.poseidon381.v1", modulus=str(P), alpha=5,
                   full_rounds=8, partial_rounds=57, skip_matrices=0,
                   ark=[[f"{v:064x}" for v in row] for row in matrices["ark"]],
                   mds=[[f"{v:064x}" for v in row] for row in matrices["mds"]], vectors=[])
        raw = json.dumps(obj, indent=2).replace("\n", "\r\n").encode("ascii")
        (directory / file).write_bytes(raw)
        params = dict(width=width, **matrices)
        canonical += _table(label + "Canonical", params, "Nat")
        positions = iter(re.finditer(rb'"([0-9a-f]{64})"', raw))
        for kind in ("ark", "mds"):
            for r, row in enumerate(matrices[kind]):
                for c, value in enumerate(row):
                    token = next(positions)
                    begin, end = token.span(1)
                    records.append(dict(file=file, table=kind, row=r, column=c,
                        raw_content_begin=begin, raw_closing_quote=end, raw_next_cursor=end + 1,
                        lf_content_begin=len(raw[:begin].replace(b"\r\n", b"\n")),
                        literal=f"{value:064x}", canonical_integer=str(value),
                        bytes_be=list(value.to_bytes(32, "big")),
                        canonical_namespace="RuntimeNativePoseidonParameters." + label + "Canonical",
                        serde_plain_branch=True))
        assert next(positions, None) is None
    return canonical, records


class LiteralJoinTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.canonical, self.records = fixture(self.root)

    def test_ordered_literals_and_scope(self):
        result = generate(self.root, self.canonical, self.records)
        self.assertEqual(result["literal_count"], 630)
        self.assertEqual(len(result["modules"]), 5)
        self.assertFalse(result["qualification"])
        self.assertFalse(result["certification"])
        self.assertEqual(result["evidence"], [])
        for name, source in result["modules"].items():
            if name != "RuntimeNativeParameterLiteralArtifact":
                self.assertIn("exact raw_codec_entries row column", source)
            else:
                self.assertIn("rw [small_source_artifact]", source)
                self.assertIn("ShielddHexArtifactLoader.wide_source_object", source)
            self.assertNotIn("native_decide", source)
            self.assertNotIn("Satisfies", source)

    def test_position_value_order_and_byte_mutations_refused(self):
        for key, value in (("raw_content_begin", 0), ("lf_content_begin", 0),
                           ("raw_next_cursor", 0), ("canonical_integer", "2"),
                           ("bytes_be", [0] * 32), ("serde_plain_branch", False)):
            records = copy.deepcopy(self.records)
            records[0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                checked(self.root, self.canonical, records)
        records = copy.deepcopy(self.records)
        records[0], records[1] = records[1], records[0]
        with self.assertRaises(ValueError):
            checked(self.root, self.canonical, records)

    def test_closed_record_types(self):
        for key, value in (("row", False), ("column", 0.0), ("bytes_be", None),
                           ("bytes_be", [False] + [0] * 31), ("serde_plain_branch", 1)):
            records = copy.deepcopy(self.records)
            records[0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                checked(self.root, self.canonical, records)
        records = copy.deepcopy(self.records)
        records[0]["wanted_hash"] = 1
        with self.assertRaises(ValueError):
            checked(self.root, self.canonical, records)

    def test_canonical_table_and_actual_artifact_refusals(self):
        with self.assertRaises(ValueError):
            checked(self.root, self.canonical.replace("| 0 => 1", "| 0 => 2", 1), self.records)
        with self.assertRaises(ValueError):
            checked(self.root, self.canonical + self.canonical, self.records)
        path = self.root / "poseidon381.json"
        raw = path.read_bytes()
        path.write_bytes(raw.replace(b'"alpha": 5', b'"alpha": true'))
        with self.assertRaises(ValueError):
            checked(self.root, self.canonical, self.records)

    def test_parser_full_source_controls(self):
        for raw in (b'{"x":1,"x":2}', b'{"x":"\\u0030"}', b'[] false', b'[01]',
                    b'[1,]', b'"unterminated', b'"\xff"'):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                SourceParser(raw).document()
        token = SourceParser(b'{"unknown":[false,null,3],"x":"ok"}').document()
        self.assertEqual(token.kind, "object")


if __name__ == "__main__":
    unittest.main()
