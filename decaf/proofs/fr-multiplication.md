# Rust Fr multiplication

`python3 decaf_fr_field_proof.py` requires a fresh accepted 64-root Fq native
receipt, the pinned generation and Fiat build receipts, and the adopted Rust
candidate source. It performs fresh Fr extraction and checks 39 Fr theorem roots
with closed transitive assumptions and recursive VM-free kernel checking.

The theorem covers the entire extracted `fr_mul`, including all seven repeated
rounds and final canonical subtraction/selection. It requires eight canonical
u32 words in each input, an eight-word output buffer, and `0 <= b < r`. It proves
canonical output and `2^256 * out = a * b + r * k` for an integer `k`, independently
of the initial output buffer. The stronger model domain for `a` does not broaden
the native library's reduced-input contract.

Fr's low modulus limb is 3275741695. Its Montgomery coefficient uses
1893980673, whose product with that limb plus one is `2^32 * 1444525891`.
Each reduction accounts for nine products and sixteen carries. Helper and
first-row reuse is justified by equality of the actual extracted Fr and Fq
definitions. The proof retains the ninth accumulator word until its bound
justifies removing it.

`decaf_fr_native_prefix.py` derives eleven checkpoint modules. Inventory and
variable-reference guards are diagnostic checks; `FrTail.v` and `FrComplete.v`
prove the actual source connections. The runner requires source mutations of
the coefficient, discarded carry, and final selection, plus a generated suffix
connection mutation. Native witnesses stay within the reduced-input contract.
The discarded-carry mutant must fail its explicit propagation guard; this is
reported separately from arithmetic proof rejection. Missing evidence, unrelated
compiler errors, timeouts and interrupted jobs cannot pass a control.

The runner binds source, matrix, generation, parent proof, compiler/import and
extraction-dispatch identities before and after replay. Reports are refreshed
atomically under `.work/decaf-fr-field-proof`, with separate bounded logs and
proof-artifact storage. Local compilation and experimental kernel checks do not
substitute for this fresh replay.

These are arithmetic theorems in the supplied total `Core` model. Native
execution/extraction semantics, overflow/panic safety, termination, the exact
Fiat Fr endpoint, other field operations, compiled traces and consumer/protocol
closure remain separate obligations. `full_certification` remains false.
