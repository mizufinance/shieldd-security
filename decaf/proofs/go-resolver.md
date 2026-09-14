# Go field dispatch construction

`decaf_go_resolver_proof.py` consumes a complete, current
`decaf_go_field_proof.py` replay and generates a concrete field dispatch table
from its exact Goose extraction bytes. Run it after the field replay:

```sh
python3 decaf_go_resolver_proof.py
```

Its three audit roots cover:

- One record containing the four generated named-type contracts and 35 function
  unfolding contracts: 32 generated field functions and `math/bits.Add64`,
  `Sub64`, and `Mul64`.
- The existing Fq addition theorem instantiated with that dispatch.
- The existing Fr addition theorem instantiated with that dispatch.

The function contracts identify the actual extracted bodies. They do not prove
arithmetic correctness of all 32 functions. Nonempty type arguments and unknown
function names resolve to `func.nil`; this is not a native panic or rejection
theorem. Other named types remain unchanged by this field-only normalization.

The construction retains the non-dispatch fields of an explicit base
`GoSemanticsFunctions` record. Function unfolding uses an explicit function-value
encoding contract. The addition connection requires `PreSemantics` for the
**modified** dispatch instance. It does not infer this compatibility from a base
`PreSemantics` instance, and it does not construct `GoGlobalContext`,
`GoLocalContext`, or the full `PreSemantics` model. Native execution correspondence
and termination remain required.

The generator checks exact declaration inventories and preserves raw extraction
bytes, including non-UTF-8 bytes in Goose string literals. The replay binds its
generator, handwritten connection, generated sources, parent evidence, and
compiled artifacts. Parent validation checks the complete source/tool inventory,
fresh Perennial build, exact Fiat generation, source/proof copies, reconstructed
audit, required compiled helper prefixes, and native/proof control logs.

A changed underlying type and an addition-to-subtraction dispatch mutation must
each fail at its exact contract equation. Interruptions, timeouts, missing imports,
ambiguous command logs, and errors at another proof site cannot satisfy these
controls. Successful compilation, closed-global-assumption audits, recursive
kernel checking, controls, and final freshness checks are all required for an
atomic passing receipt. Rocq VM/compiler trust is explicit.

Evidence is written under `.work/decaf-go-resolver-proof`.
`full_certification` remains false.
