import hashlib
import unittest

import decaf_go_specialization as spec
import decaf_go_resolver_proof as replay


class GoSpecializationTests(unittest.TestCase):
    def sources(self):
        def declarations(names, types=()):
            text = "".join(f'Definition {name} {{ext : ffi_syntax}} {{go_gctx : GoGlobalContext}} : go_string := "{name}".\n'
                           for name in (*types, *names))
            text += "".join(f"Definition {name}ⁱᵐᵖˡ {{ext : ffi_syntax}} {{go_gctx : GoGlobalContext}} : val := #().\n"
                            for name in names)
            text += "".join(f"Definition {name}ⁱᵐᵖˡ {{ext : ffi_syntax}} : go.type := word.\n" for name in types)
            return text.encode()
        return declarations(spec.FIELD_NAMES, spec.TYPE_NAMES), declarations(spec.BIT_NAMES)

    def test_exact_inventory_and_raw_byte_binding(self):
        field, bits = self.sources()
        result = spec.render(field, bits)
        self.assertEqual(tuple(result), spec.GENERATED)
        self.assertEqual(len(spec.ROOTS), len(set(spec.ROOTS)))
        for output in result.values():
            self.assertIn(hashlib.sha256(field).hexdigest(), output)
            self.assertIn(hashlib.sha256(bits).hexdigest(), output)
        self.assertNotEqual(result, spec.render(field, bits + b"\n\x80\x00\xff"))
        for changed in (field.replace(b"FqMul", b"OtherMul"),
                        field + "Definition FqMulⁱᵐᵖˡ {ext : ffi_syntax} : val := body.\n".encode()):
            with self.assertRaises(ValueError):
                spec.render(changed, bits)

    def test_literal_scope_is_explicit_and_unsupported_forms_reject(self):
        self.assertEqual(spec.explicit_body("#() #(W64 2) #(W8 3) #63 #true #false"),
                         "(encode Unit tt) (encode Uint64 (W64 2)) (encode Uint8 (W8 3)) (integer_literal 63) (encode Bool true) (encode Bool false)")
        for body in ('#(W32 0)', '#"string"', '#(-1)', '#pointer', '{go_gctx : GoGlobalContext}'):
            with self.assertRaises(ValueError):
                spec.explicit_body(body)

    def test_body_changes_affect_the_program_and_proof_binding(self):
        field, bits = self.sources()
        original = spec.render(field, bits)["GoFullSpecialization"]
        changed = spec.render(field.replace(b"val := #()", b"val := #(W64 9)", 1), bits)["GoFullSpecialization"]
        self.assertNotEqual(original, changed)
        self.assertIn("(encode Uint64 (W64 9))", changed)
        bodies = changed.split("Section correspondence.", 1)[0]
        self.assertNotIn("GoGlobalContext", bodies)
        for _, name in spec.ENTRIES:
            self.assertIn("Lemma specializes_" + name + " :", changed)

    def test_declarations_must_be_unique_and_complete(self):
        for source in ("", "Definition name : val := body", "Definition name : val := one.\nDefinition name : val := two.\n"):
            with self.assertRaises(ValueError):
                spec.declaration(source, "name")

    def test_callee_omission_mutates_actual_rendered_rank_table_once(self):
        field, bits = self.sources()
        source = spec.render(field, bits)["GoFieldCallRanks"]
        changed = replay.mutate(source, "omitted-callee")
        self.assertNotEqual(source, changed)
        self.assertNotIn("[literal_bits.Add64;", changed)
        with self.assertRaises(ValueError):
            replay.mutate(changed, "omitted-callee")


if __name__ == "__main__":
    unittest.main()
