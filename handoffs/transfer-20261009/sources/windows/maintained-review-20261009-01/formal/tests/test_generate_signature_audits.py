"""Nested generated proofs retain one full statement per qualified axiom audit."""
from collections import Counter
import io
import re
import unittest

from circuits.generate_hash_round import _signature_audits
from circuits import generate_transfer_fixed_spend as fixed
from circuits import transfer_fixed_spend as rows, transfer_rk_addition as addition
from tests.test_transfer_fixed_spend_rows import fixture as fixed_fixture
from tests.test_transfer_rk_addition import fixture as addition_fixture


def qualified_audits(source):
    namespaces = []
    checks, axioms = Counter(), Counter()
    for line in source.splitlines():
        if line.startswith('namespace '):
            namespaces.append(line.split()[1])
        elif line.startswith('end '):
            if not namespaces or namespaces.pop() != line.split()[1]:
                raise AssertionError('generated namespace closure changed')
        else:
            match = re.fullmatch(r'#(check @|print axioms )([A-Za-z0-9_]+)', line)
            if match:
                target = checks if match[1] == 'check @' else axioms
                target['.'.join([*namespaces, match[2]])] += 1
    return checks, axioms


class SignatureAuditTests(unittest.TestCase):
    def assert_single_qualified_audits(self, source):
        checks, axioms = qualified_audits(source)
        self.assertTrue(axioms)
        self.assertEqual(checks, axioms)
        self.assertEqual(set(checks.values()), {1})

    def test_nested_pass_is_idempotent_and_keeps_namespace_identity(self):
        plain = ('namespace Inner\n#print axioms constantLink\nend Inner\n'
                 'namespace Outer\n#print axioms constantLink\nend Outer\n')
        once = _signature_audits(plain)
        self.assertEqual(_signature_audits(once), once)
        self.assert_single_qualified_audits(once)
        self.assertEqual(set(qualified_audits(once)[0]),
                         {'Inner.constantLink', 'Outer.constantLink'})

    def test_actual_nested_fixed_and_rk_generators_have_single_audits(self):
        for start in (0, 1):
            data, accepted, stream = fixed_fixture(window_start=start)
            extracted = rows.extract_rows(data, accepted, stream)
            with self.subTest(window=start):
                self.assert_single_qualified_audits(fixed.generate_window(data, accepted, extracted))
        data, accepted, ordinary = addition_fixture()
        extracted = addition.extract(data, accepted, lambda: io.BytesIO(ordinary))
        self.assert_single_qualified_audits(addition.generate(data, accepted, extracted))


if __name__ == '__main__':
    unittest.main()
