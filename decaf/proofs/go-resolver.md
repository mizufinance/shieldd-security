# Go field dispatch construction

`decaf_go_resolver_proof.py` consumes a complete, current
`decaf_go_field_proof.py` replay and generates a concrete field dispatch table
from its exact Goose extraction bytes. Run it after the field replay:

```sh
python3 decaf_go_resolver_proof.py
```

Its 24 audit roots cover:

- One record containing the four generated named-type contracts and 35 function
  unfolding contracts: 32 generated field functions and `math/bits.Add64`,
  `Sub64`, and `Mul64`.
- The existing Fq addition theorem instantiated with that dispatch.
- The existing Fr addition theorem instantiated with that dispatch.
- Constructive value encoding and decoding, bounded array indexing, replacement
  and frame preservation, and function/nested-tuple round trips.
- Literal word-array ownership, window split/restore, single-element replacement,
  and the dynamic length invariant of `array.t w64 4`.

`GoFieldEncoding.v` and `GoFieldMemory.v` do not require `GoGlobalContext` or
`PreSemantics`. The latter uses explicit literal encodings and the ordinary
non-atomic heap ghost-state interface. These foundations are not yet a
specialized execution semantics for the extracted field bodies. The connection
to the existing conditional addition theorems retains its original assumptions.
The array decoder enforces lengths; signed and unsigned 64-bit representations
share a word encoding, and injectivity is per representation. Strings retain
raw bytes. No cross-representation disjointness or whole-language encoding is
claimed.
`replace_at` is a pure list update whose out-of-bounds case is a no-op; it is
not the Go indexing/panic semantics. Memory addresses count abstract heap cells,
not native bytes. Each owned cell uses the ordinary non-null heap points-to
predicate, while an empty array owns no cells. Allocation validity and the
native pointer/address correspondence remain execution-bridge obligations.

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

Two additional controls remove the array decoder's length check and double the
word-address spacing. They must fail the empty-four-word-array rejection and
one-word-address equations respectively, at their exact proof sites.

Evidence is written under `.work/decaf-go-resolver-proof`.
`full_certification` remains false.
