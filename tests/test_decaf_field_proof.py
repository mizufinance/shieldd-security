import unittest

import decaf_field_proof as proof


def extraction():
    array = "t_Array (t_u32) ((8 : t_usize))"
    body = f"Definition fq_add (out1 : {array}) (arg1 : {array}) (arg2 : {array}) : {array} :=\n"
    body += "\n".join(f"f_index ({name}) (({i} : t_usize))" for i in range(8) for name in ("arg1", "arg2"))
    body += "\n" + "\n".join(f"update_at_usize (out1) (({i} : t_usize))" for i in range(8))
    body += "\n" + "fq_addcarryx_u32 " * 8 + "fq_subborrowx_u32 " * 9 + "fq_cmovznz_u32 " * 8 + "cast.\n"
    return body


class NativeFieldProofTests(unittest.TestCase):
    def test_access_schedule(self):
        proof.validate_accesses(extraction())
        for changed in (
                extraction().replace("f_index (arg1) ((7", "f_index (arg1) ((8"),
                extraction().replace("f_index (arg1) ((7", "f_index (arg1) ((6"),
                extraction().replace("update_at_usize (out1) ((7", "update_at_usize (out1) ((6"),
                extraction().replace("cast.", "cast f_sub."),
                extraction().replace("fq_cmovznz_u32", "fq_unknown", 1),
                extraction().replace("(8 : t_usize)", "(9 : t_usize)", 1),
                extraction() + "Admitted.\n"):
            with self.assertRaises(ValueError):
                proof.validate_accesses(changed)

    def test_modulus_mutation_is_confined(self):
        line = "fq_subborrowx_u32(&mut x17, &mut x18, 0x0, x1, (0x1 as u32));"
        source = line + "\npub const fn fq_add() {\n" + line + "\n}\n" + line
        self.assertEqual(proof.modulus_mutation(source).count("0x2 as"), 1)
        with self.assertRaises(ValueError):
            proof.modulus_mutation("pub const fn fq_add() {\n}\n")

    def test_field_rejection_requires_arithmetic_failure(self):
        proof.validate_rejection('File "RustFieldAdd.v":\nError: Tactic failure: Cannot find witness.')
        for text in ('File "RustFieldAdd.v":\nError: Cannot infer a type',
                     'File "Core.v":\nError: Tactic failure: Cannot find witness.'):
            with self.assertRaises(ValueError):
                proof.validate_rejection(text)

    def test_assumptions_must_be_exactly_closed(self):
        proof.validate_assumptions("Closed under the global context\n" * len(proof.ROOTS))
        with self.assertRaises(ValueError):
            proof.validate_assumptions("Axioms: arithmetic\n")


if __name__ == "__main__":
    unittest.main()
