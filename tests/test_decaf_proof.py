import unittest
import decaf_proof


class ProofGateTests(unittest.TestCase):
    def test_closed_roots(self):
        decaf_proof.validate_assumptions("Closed under the global context\n" * len(decaf_proof.ROOTS))

    def test_incomplete_or_assumed_roots_fail(self):
        for text in ("", "Closed under the global context\n", "Axioms:\nunsafe_arithmetic : True",
                     "Closed under the global context\n" * len(decaf_proof.ROOTS) + "Error: missing theorem"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                decaf_proof.validate_assumptions(text)

    def test_infrastructure_failure_is_not_mutation_detection(self):
        for text in ("", "Killed", "Carry.v\nError: Cannot find a physical path bound to logical path Core"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                decaf_proof.validate_proof_rejection(text)

    def test_theorem_rejection(self):
        decaf_proof.validate_proof_rejection('File "Carry.v", line 30\nError: Unable to unify')

    def test_unsupported_extraction(self):
        for placeholder in ("failure", "Admitted", "Axiom", "NotImplementedYet", "TODO"):
            with self.subTest(placeholder=placeholder), self.assertRaises(ValueError):
                decaf_proof.validate_extraction(placeholder)

    def test_safety_inventory_detects_added_operation(self):
        text = "Definition fq_addcarryx_u32 := f_add f_add f_bitand f_shr cast cast cast cast cast."
        decaf_proof.validate_extraction(text)
        with self.assertRaises(ValueError):
            decaf_proof.validate_extraction(text + " f_add")

    def test_mutation_must_match_exactly(self):
        with self.assertRaises(ValueError):
            decaf_proof.shift_mutation("unrelated source")
        source = "let x3: FqU1 = ((x1 >> 32) as FqU1);"
        self.assertIn(">> 33", decaf_proof.shift_mutation(source))
        with self.assertRaises(ValueError):
            decaf_proof.shift_mutation(source + source)
