"""Source/certificate correspondence guards, independent of descriptor hashing."""
import copy
import unittest

from circuits.generate_long_recipe import validate_descriptor


class LongRecipeDescriptorTests(unittest.TestCase):
    def setUp(self):
        self.data = {
            "constants": [{"source_constant": 7, "integer": 2}],
            "inputs": [{"source_witness": 0, "compiler_column": 3, "terms": [[3, 1]]}],
            "nodes": [{
                "source_node": 10, "operation": "mul", "left": [0, 7], "right": [1, 0],
                "expression": {"kind": "linear"},
                "certificate": {
                    "node": 10, "constructor": "foldedLeft", "left": [0, 7],
                    "right": [1, 0], "coefficient": 2, "rows": [],
                },
            }],
        }

    def test_matching_raw_operation_and_certificate(self):
        validate_descriptor(self.data)

    def test_correspondence_mutations_are_rejected(self):
        mutations = [
            lambda d: d["nodes"][0].update(operation="add"),
            lambda d: d["nodes"][0]["certificate"].update(constructor="add"),
            lambda d: d["nodes"][0]["certificate"].update(right=[1, 1]),
            lambda d: d["nodes"][0]["certificate"].update(coefficient=3),
            lambda d: d["nodes"][0]["certificate"].update(rows=[2]),
            lambda d: d["inputs"][0].update(compiler_column=4),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                changed = copy.deepcopy(self.data)
                mutate(changed)
                with self.assertRaises(ValueError):
                    validate_descriptor(changed)


if __name__ == "__main__":
    unittest.main()
