"""Retained AST export/generator correspondence, not a new Rust or Lean proof."""
import hashlib
import json
from pathlib import Path
import unittest
from circuits import statement_projection

ROOT = Path(__file__).resolve().parents[1]

class StatementProjectionTests(unittest.TestCase):
    def export(self):
        data = (ROOT / 'circuits/evidence/pr160-statement-projection.json').read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(),
                         '8c963574f036f5b7963d434fb4dbd0624acd446c6426525b91c3d9a11200b7fa')
        return json.loads(data)

    def test_retained_export_reproduces_audited_generated_source(self):
        expected = (ROOT / 'circuits/ShielddSecurity/RuntimeTransferStatement.lean').read_bytes()
        self.assertEqual(hashlib.sha256(expected).hexdigest(),
                         '17f73cfc7163c6c8ff0adebeaa075504310926c0e030d6ca8393fe3d731f43fe')
        self.assertEqual(statement_projection.generate(self.export()).encode('utf-8'), expected)

    def test_semantically_changed_role_order_is_rejected(self):
        result = statement_projection.controls(self.export())
        self.assertEqual(len(result['rejected']), 4)

if __name__ == '__main__':
    unittest.main()
