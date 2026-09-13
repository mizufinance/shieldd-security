import copy
import unittest

import decaf
from decaf_shieldd_binary import resolved_decaf, address_control_leaks


class ResolvedDependencyTests(unittest.TestCase):
    def test_address_control_requires_memory_leak_in_injected_function(self):
        memory = '[checkct:result] Instruction 0x401020 has memory access leak (0.1s)'
        self.assertEqual(address_control_leaks(memory, 0x401010, 32), [0x401020])
        for log, size in ((memory.replace('memory access', 'control flow'), 32),
                          (memory.replace('0x401020', '0x402000'), 32),
                          (memory.replace('0x401020', '0x401030'), 32),
                          ('Program status is : insecure', 32), (memory, 0)):
            with self.subTest(log=log, size=size), self.assertRaises(decaf.Blocked):
                address_control_leaks(log, 0x401010, size)

    def setUp(self):
        self.expected = {"repository": "https://example.invalid/decaf.git", "revision": "a" * 40}
        source = "git+https://example.invalid/decaf.git?rev=" + "a" * 40 + "#" + "a" * 40
        self.metadata = {
            "packages": [{"id": "ka", "name": "decaf377-ka"},
                         {"id": "selected", "name": "decaf377", "version": "0.10.1", "source": source},
                         {"id": "unrelated", "name": "decaf377", "version": "0.10.1", "source": "registry+other"}],
            "resolve": {"nodes": [{"id": "ka", "deps": [{"name": "decaf377", "pkg": "selected"}]}]},
        }

    def test_selects_actual_ka_edge_among_multiple_decaf_packages(self):
        self.assertEqual(resolved_decaf(self.metadata, self.expected)["id"], "selected")

    def test_cargo_canonical_git_suffix(self):
        self.metadata["packages"][1]["source"] = self.metadata["packages"][1]["source"].replace(".git?", "?")
        self.assertEqual(resolved_decaf(self.metadata, self.expected)["id"], "selected")

    def test_stale_lock_does_not_claim_matrix_identity(self):
        for mutation in ("edge", "revision", "repository", "omission", "duplicate"):
            with self.subTest(mutation=mutation):
                value = copy.deepcopy(self.metadata)
                deps = value["resolve"]["nodes"][0]["deps"]
                if mutation == "edge":
                    deps[0]["pkg"] = "unrelated"
                elif mutation == "revision":
                    value["packages"][1]["source"] = value["packages"][1]["source"].replace("a" * 40, "b" * 40)
                elif mutation == "repository":
                    value["packages"][1]["source"] = value["packages"][1]["source"].replace("example.invalid", "other.invalid")
                elif mutation == "omission":
                    deps.clear()
                else:
                    deps.append(dict(deps[0]))
                with self.assertRaises(decaf.Blocked):
                    resolved_decaf(value, self.expected)


if __name__ == "__main__":
    unittest.main()
