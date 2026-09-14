import unittest

from decaf_go_resolver import BIT_NAMES, FIELD_NAMES, TYPE_NAMES, render


class GoResolverTests(unittest.TestCase):
    def sources(self):
        fields = "\n".join(f"Definition {name}ⁱᵐᵖˡ {{ext : ffi_syntax}} : val := body."
                           for name in FIELD_NAMES)
        fields += "\n" + "\n".join(f"Definition {name}ⁱᵐᵖˡ {{ext : ffi_syntax}} : go.type := word."
                                    for name in TYPE_NAMES)
        bits = "\n".join(f"Definition {name}ⁱᵐᵖˡ {{ext : ffi_syntax}} : val := body."
                         for name in BIT_NAMES)
        return fields, bits

    def test_exact_inventory_rejects_renaming_omission_and_duplication(self):
        fields, bits = self.sources()
        render(fields.encode(), bits.encode())
        for changed in (fields.replace("FqMulⁱᵐᵖˡ", "OtherMulⁱᵐᵖˡ"),
                        fields.replace("Definition FqMul", "Omitted FqMul"),
                        fields + "\n" + fields.splitlines()[0],
                        fields.replace("FrUint1ⁱᵐᵖˡ", "OtherTypeⁱᵐᵖˡ")):
            with self.assertRaises(ValueError):
                render(changed.encode(), bits.encode())
        for changed in (bits.replace("Mul64ⁱᵐᵖˡ", "Mul32ⁱᵐᵖˡ"),
                        bits + "\n" + bits.splitlines()[0]):
            with self.assertRaises(ValueError):
                render(fields.encode(), changed.encode())

    def test_source_body_change_changes_generated_binding(self):
        fields, bits = self.sources()
        original = render(fields.encode(), bits.encode())
        self.assertNotEqual(original, render(fields.replace(":= body.", ":= changed.", 1).encode(), bits.encode()))
        self.assertNotEqual(original, render(fields.encode(), bits.replace(":= body.", ":= changed.", 1).encode()))
        self.assertNotEqual(original, render(fields.encode(), bits.encode() + b'\n\x80\xff'))
        with self.assertRaises(TypeError):
            render(fields, bits)
