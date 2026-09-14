# Go field dispatch construction

`decaf_go_resolver_proof.py` consumes a complete, current
`decaf_go_field_proof.py` replay and generates a concrete field dispatch table
from its exact Goose extraction bytes. Run it after the field replay:

```sh
python3 decaf_go_resolver_proof.py
```

Its 317 audit roots cover:

- One record containing the four generated named-type contracts and 35 function
  unfolding contracts: 32 generated field functions and `math/bits.Add64`,
  `Sub64`, and `Mul64`.
- The existing Fq addition theorem instantiated with that dispatch.
- The existing Fr addition theorem instantiated with that dispatch.
- Constructive value encoding and decoding, bounded array indexing, replacement
  and frame preservation, and function/nested-tuple round trips.
- Literal word-array ownership, window split/restore, single-element replacement,
  and the dynamic length invariant of `array.t w64 4`.
- Specialization of all 32 extracted field bodies and three reached word helpers
  to explicit literal and control-combinator encodings.
- Syntactic inclusion and decreasing direct-call ranks for those 35 bodies.
- A concrete dispatcher with unique names and exact body equations for all 35
  entries, plus explicit control, integer-literal, and empty-FFI foundations.

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

`decaf_go_specialization.py` generates four proof modules from the same exact
extraction bytes as the resolver. The specialized bodies use a concrete empty
external-interface syntax and do not require `GoGlobalContext`. Their equality
to the old extracted bodies is conditional on explicit unit, string, boolean,
word, byte, and untyped-integer encoding hypotheses. The equality proofs do not
establish an inhabitant of that old universal interface.

Untyped integers use an injective tagged syntax representation. Its
location-shaped payload is data, not a heap address, and must never be accepted
by the eventual pointer decoder. The syntax filter rejects unsupported
constructors and checks named calls, but permits variables, applications and
arbitrary operand types; it is not a typing or binding-closure proof. Call ranks
and exact dispatch equations do not supply instruction semantics, safe memory
access, progress, termination or native execution correspondence. Empty FFI
supplies neither a language semantics nor adequacy.

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
Three specialization controls alter the first Fq addition input index, omit
`bits.Add64` from the callee rank table, and map Fq addition to the subtraction
body. They must fail the corresponding source-body equality, ranked-call check,
and exact dispatch-body equation. Their dependencies are the freshly compiled
original case and remain in the same evidence closure.

Evidence is written under `.work/decaf-go-resolver-proof`.
`full_certification` remains false.

The explicit field-machine extension checks scalar representations and supported
conversions, including constant representability and exact pointer-type guards.
It supplies checked array references, a finite abstract block heap, an evaluator,
fuel monotonicity, and soundness into a finite execution relation. The actual
specialized Add64, Sub64, Mul64 and Fq conditional-move bodies have execution
equations in this machine. Shared arithmetic lemmas establish carry/borrow
correctness for one-bit carry inputs and the full 128-bit helper product.
All 35 specialized bodies also have instruction/type-shape checks.

These results do not establish Go/Goose adequacy or native execution correspondence.
The shape check does not prove operand typing, constant ranges, shift counts,
memory validity or field-body progress. The evaluator currently rejects unsupported
operations and merges errors with fuel exhaustion as `None`; fuel bounds depth,
not total steps. Successful helper equations project away the final heap except
for the conditional-move write and the explicit pair-allocation-order equation.
The block heap uses unbounded abstract addresses; native address bounds, allocation
behavior, runtime concurrency and heap/pointer wellformedness remain obligations.
No full Fq/Fr multiplication execution theorem is claimed by this extension.

Four additional negative controls widen the byte-constant range, remove the
pointer-type guard, reverse pair evaluation order, and replace word addition
with subtraction. Each compiles fresh prerequisites and must fail its exact
constant-rejection, pointer-rejection, effectful allocation-order or actual-helper
execution proof. This extension is replayed from source alongside the dispatch
proofs; copied experimental objects cannot satisfy its evidence closure.

The framing extension proves prefix-preserving heap relocation, including
pointer-valued scalar cells, checked array references, pure operations, and all
35 dispatched function bodies. Successful execution preserves the supported
expression/value fragment. Evaluation commutes with this relocation at the same
fuel, including `None`; this is not a progress or failure-classification theorem.
The fragment predicate admits unknown resolver names, which may fail to resolve.
Arrays and sum payloads are not recursively relocated; tagged integer literals
remain data rather than addresses.

The actual Add64, Sub64 and Mul64 calls consequently execute in arbitrary existing
abstract heaps, preserving the prefix and appending existential local blocks.
No allocation count, reclamation, resource bound, native memory behavior or full
Fq/Fr multiplication theorem follows from these corollaries. Two additional
controls change the pointer-prefix displacement and incorrectly relocate tagged
integer data; both must fail their exact control lemmas.

Proof compilation disables only Rocq's `level-tolerance` notation-deprecation
warning. Its repetition exceeded the bounded replay output budget; all other
warnings, proof errors and the output cap remain enabled. The diagnostic flag is
recorded in every compilation command, and a failed/interrupted replay remains
incomplete regardless of earlier successful stages.

The resolver replay retains fresh compiled objects for every control. It permits
512 MiB for the entire run, including every log, and limits each command log to
16 MiB. Both limits are checked before, during and after commands; a resource
failure cannot count as an expected proof rejection, even if the process exits
with status 1. Timeouts terminate the process group. The shared fuzz-runner
100 MiB budget is unchanged. The earlier 317-root run that exceeded that aggregate
budget remains failed; successful earlier stages do not complete its receipt.
