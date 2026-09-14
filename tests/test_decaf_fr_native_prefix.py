import unittest

import decaf_fr_native_prefix as generator


def fixture():
    def marker(i):
        return f"  let x{i} : t_u32 := (0 : t_u32) in\n"
    text = "Definition fr_mul :=\nlet initial := 0 in\n" + marker(40)
    for index, start in enumerate(range(91, 698, 101)):
        prior = 75 if index == 0 else start - 17
        top = "(cast (x90))" if index == 0 else f"(x{start-1})"
        text += marker(start) + f"let digit := x{index+1} in\nlet low := x{prior} in\nlet top := {top} in\n"
        text += marker(start + 31) + marker(start + 49)
    return text + marker(798) + "out1.\n"


class FrCheckpointTests(unittest.TestCase):
    def test_complete_inventory_and_tail_preservation(self):
        result = generator.multiplication_checkpoints(fixture())
        self.assertEqual(set(result), {name + ".v" for name in generator.DERIVED_MODULES})
        self.assertIn("let digit := x7", result["FrSuffixDefinition1.v"])
        self.assertIn("let x798", result["FrFinalDefinition.v"])

    def test_missing_duplicate_and_reordered_boundaries_fail(self):
        source = fixture()
        marker = "  let x192 : t_u32 := (0 : t_u32) in\n"
        for changed in (source.replace(marker, ""), source.replace(marker, marker * 2),
                        source.replace(marker, "").replace("  let x91", marker + "  let x91")):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                generator.multiplication_checkpoints(changed)

    def test_cross_round_reference_collisions_fail(self):
        source = fixture()
        for old, new in (("let digit := x7", "let digit := x1"),
                         ("let low := x680", "let low := x75")):
            self.assertEqual(source.count(old), 1)
            with self.assertRaisesRegex(ValueError, "unexpected cross-round"):
                generator.multiplication_checkpoints(source.replace(old, new))

    def test_changed_local_round_shape_fails(self):
        source = fixture().replace("let digit := x7", "let digit := x7 in let extra := x697")
        with self.assertRaisesRegex(ValueError, "reviewed shape"):
            generator.multiplication_checkpoints(source)

    def test_malformed_body_and_carry_interface_fail(self):
        for changed in ("", fixture().replace("out1.", "other."),
                        fixture().replace("(cast (x90))", "x90")):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                generator.multiplication_checkpoints(changed)
