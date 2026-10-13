# ARM source-model wide Montgomery reduction

Runtime: `844389ee069e1fb2e576708842d0b389b4d9a44a`. Original desktop packet: `d0d7063839df86896a504bfdf3dd5fa0d5ee4f32`.

The modeled `redc_mont_256` reduces the low four words before adding the high four words and retaining the fifth carry and borrow. For every raw high-half word vector, it derives the exact single-subtraction normalization, four output words and the weighted modular relation for the entire wide input.

Atomic reconciliation authenticates ten complete type and axiom audits and 280 dependency sources, with original successful receipts and immutable plan/runner metadata. Eight runtime files match the exact snapshot; locked BLST context matches the reviewed predecessor.

This establishes source-model arithmetic. It does not establish inverse correctness, canonicality for unrestricted wide inputs, or actual selected-backend/compiler/ISA execution. All full Transfer endpoints remain OPEN; native certification credit is zero.
