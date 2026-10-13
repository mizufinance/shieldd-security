# ARM source-model inverse tail

Runtime: `844389ee069e1fb2e576708842d0b389b4d9a44a`. Original desktop packet: `14cbf03ab3152de237ace80896c76a74df01c953`.

Arbitrary observed low/high words pass through the modeled ARM reduction and rRR-left CIOS multiplication. The result has canonical words, satisfies the weighted field relation for the entire observed wide input, and yields the modeled caller's 32 field bytes.

Atomic reconciliation authenticates six complete type and axiom audits and 281 dependency sources. Eight runtime files match the exact snapshot. Five inverse source files were independently checked against the locked BLST 0.3.17 archive with checksum `c20659f9bbee16cbbd2f7393e40ab6309f5a98f76a2eb57a995ec508b72387fe`.

The ct-inverse recurrence and inverse identity are still open, as are actual compiler/ISA/ABI and private-value correspondence. All full Transfer endpoints remain OPEN; native certification credit is zero.
