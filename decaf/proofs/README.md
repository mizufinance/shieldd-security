# Source-linked Decaf proofs

The shared specification uses Rocq. Native field generation uses the pinned
Fiat-Crypto source with the checked-in array-index printer patch; Rust and Go
retain native implementations. Proof extraction
is a trusted translation boundary, with the exact executable identity recorded.
The implementation program is tracked by issues #2 and #4–#6.

## Exact-option Fiat multiplication pipeline

```sh
python3 decaf_fiat_build.py --build-parent /absolute/native/build/cache
python3 decaf_fiat_proof.py
python3 -m unittest discover -s tests -p 'test_decaf_fiat_*.py'
```

The first runner exports the pinned Fiat source and recursive committed
dependencies into a fresh directory, applies the checked printer patch and
rebuilds proof imports with one worker. No existing compiled proof objects are
copied. It records source and artifact identities; the proof runner rejects
stale, changed or additional local proof/plugin artifacts. Rocq, OCaml, their
installed standard library and the OS build tools remain an explicit trusted
toolchain boundary.

`FiatMultiply.v` constructs Fq and Fr typed multiplication bodies under the
Rust32 and Go64 pipeline options used by the generation recipe. The replay
checks eight theorem roots, the configured numerical moduli, transitive global
assumptions and recursive Rocq checking with VM reduction enabled. The latter
explicitly trusts Rocq's bytecode compiler and VM in conversion checking; it
does not skip checking imported dependencies. VM-free checking exceeded the
bounded local memory budget. It binds the complete generation commands and
output bytes, including the Go helper-selection flags.

This proves typed-pipeline arithmetic only. The Go `cmovznz-by-mul` helper is
outside that pipeline option record. Correspondence to printed source,
emitted helpers, language execution, native safety/termination and compiled
traces remains required. Neither a successful typed replay nor matching source
hashes closes the native multiplication gate. Reports remain scoped with
`full_certification: false`.

## Rust carry proof

```sh
python3 decaf_proof.py
python3 -m unittest discover -s tests -p test_decaf_proof.py
```

The runner fetches the exact Rust candidate from `decaf/inputs.json`, copies its
unaltered Fiat source into an isolated crate, and extracts the actual
`fq_addcarryx_u32` body. It checks three theorem roots against the dedicated
finite-word semantics in `rocq/Core.v`, rechecks the compiled proof with the
Rocq kernel checker, and requires an empty transitive assumption set.

The theorem establishes exact outputs, canonical limbs, bit-valued carry,
reconstruction, and the overflow/shift bounds for this body. The operation
inventory detects drift from this independently reviewed body; it is not a
general safety coverage proof. Changed expressions require reviewing and proving
their safety obligations. Mutable output references are
distinct under Rust's safe borrowing rules, and input words are passed by value.
This functional proof does not establish a leakage trace property.

The negative case changes the actual source shift from 32 to 33. It must both
fail the executable carry witness and fail theorem checking after a fresh
successful extraction. Compiler errors, process termination, and missing imports
cannot satisfy this control. Original and mutated evidence remain separate.

Reports, extracted code, proof objects, and logs are generated under
`.work/decaf-proof`. The report's `full_certification` remains false: field,
group, encoding, Go, and consumer theorem closure are separate requirements.

## Tool environment

`toolchain.json` pins the source/tool identities and selected representations.
The current carry replay uses native ARM64 macOS extraction artifacts, the
`hax-0.3.7` opam switch, Rust 1.89.0 for its executable witness, and a `decaf-fv`
opam switch with OCaml 5.3.0, Rocq runtime 9.2.0 and standard library 9.1.0.
It requires the pinned `record_update` checkout at `.cache/record-update`.
Other host artifacts need their own reviewed identities before use.

Native runners select artifacts by host (`aarch64-apple-darwin` or
`x86_64-unknown-linux-gnu`). Additional identities belong in
`toolchain.json` under `native_builds.<host>.<fiat|hax|goose>`; each entry
requires `binary_sha256`, with the three named executable hashes for hax.
Fiat entries also require the printer patch hash. Existing Mac identities
remain supported. An unregistered host/tool pair fails closed; a local build
does not register or approve its own hash. Record exact source, patch, build
command and package versions when reviewing a new identity. Reports record
the selected host and the native-selector source hash as well as the runner
hash. Native functional replay does not prove compiled constant-time behavior.

Rust runners invoke the verified CLI by its resolved path, verify the driver
beside that CLI (where pinned hax actually loads it), and set
`HAX_ENGINE_BINARY` to the verified engine path. An inherited engine override
cannot select an unchecked executable.

Patch comparisons request seven-digit Git blob-ID abbreviations to match the
committed patches instead of relying on the configured/default abbreviation.
Git may still extend ambiguous prefixes; such a mismatch fails closed.

For full field extraction, generate arrays without field-element typedefs.
Unsupported extraction and unproved primitive semantics must be resolved in the
source/generator or the dedicated semantic support, never by editing generated
proof output or importing hax's dummy core library.

## Native field generation

Check out the pinned Fiat revision at `.cache/fiat-crypto`, initialize its
recursive submodules, and apply `fiat-array-index.patch` there. Install the
pinned `coq-core` compatibility commands alongside Rocq in `decaf-fv`, then run:

```sh
opam exec --switch=decaf-fv -- gmake -C .cache/fiat-crypto -j2 SKIP_BEDROCK2=1 standalone-unified-ocaml
python3 decaf_generate.py
```

The patch makes `--no-field-element-typedefs` emit direct Rust array access and
keeps `const fn`. It changes the printer, whose correspondence to the arithmetic
IR remains a proof obligation. The runner checks the exact source patch and
submodules, enforces the reviewed native generator and printer-patch hashes in
`toolchain.json`, and generates Fq/Fr Rust32 and
Go64 candidates under `.work/decaf-fields`. Both languages run 216 arithmetic
checks against integer-reference results, including encoding and Montgomery
conversion. These checks establish executable regression coverage.

## Shared field constants

`python3 decaf_constants_proof.py` checks `FieldConstants.v` against the exact
Fq and Fr moduli in `toolchain.json`. Explicit Pocklington certificates establish
primality; separate roots establish the 253-bit and 251-bit representation bounds.
`LimbRepresentation.v` additionally proves canonical limb splitting/joining,
round trips, preservation of the represented integer, four-word to eight-word
lengths and the shared Montgomery radix. These facts do not yet prove native
cast, shift, bitwise-OR or array execution.
The runner requires the fresh source-bound Fiat/Coqprime build, checks all sixteen
roots and their transitive assumptions, and kernel-rechecks the resulting modules.
Both altered-modulus certificates must fail the certificate checker in fresh
modules. Arithmetic factor searches supply witnesses only; they are not trusted
primality oracles. Reports remain scoped to these shared mathematical facts and
do not discharge native execution, curve order, or group refinement obligations.

## Go model obligations

The patch gives nonempty uint64 arrays executable fresh-block allocation and
checked ownership lifting. Four-word read/write, local allocation, disjoint
copy, self-copy and same-array aliasing are proved over freshly extracted Go.
Allocation has separate return and progress theorems. Generic array typing is
not assumed: allocation requires the backing list to match the array length.

Concrete byte/word offsets preserve non-null allocated bases; null-base
addresses remain unchanged. The four address algebra laws are proved without
`PreSemantics`, and the runner rejects a proof exploiting the unguarded-offset
contradiction. Indexing checks nil pointers and signed bounds before returning
an address, with native address-only panic witnesses and semantic step lemmas.
These checks establish consistency of the concrete address-law subset, not a
model of all `PreSemantics` contracts. Unsupported array sizes and other types
remain outside this four-word proof boundary.

## Go native arithmetic proofs

```sh
python3 decaf_go_proof.py
python3 -m unittest discover -s tests -p test_decaf_go_proof.py
```

The runner extracts the installed, pinned Go `math/bits.Add64`, `Sub64` and `Mul64` bodies with Goose,
then checks their execution and universal arithmetic equations with Rocq. The output
limbs reconstruct the integer sum, difference or full product, the low limb is canonical, and the carry or borrow is
0 or 1 for carry/borrow-in 0 or 1. Multiplication preserves Go’s high/low
return order and proves each intermediate fits its word. The nine theorem
roots require no global axioms.
They are parameterized by Perennial's Go semantics, heap and FFI contracts;
extraction and compiler correspondence, including compiler intrinsics, remain
explicit trusted boundaries. Goose selects Linux/AMD64 word semantics; the
source witness runs on the native host with caller intrinsics disabled.

Apply `perennial-native.patch` to the pinned Perennial checkout and build Goose
with the pinned Go toolchain. The patch provides uint64 bit-clear semantics,
typed integer-complement extraction, checked type/signature equality, and the
fixed-array indexing/store repairs.
The runner verifies the patch and executable identities and rebuilds the model
support. It requires separate carry, borrow and multiplication shift mutations to fail their native
witnesses and freshly extracted execution theorems. Reports are written under
`.work/decaf-go-proof-replay`.

This is partial functional correctness. Full termination, field/group/consumer refinement, and compiled leakage traces remain separate
obligations; `full_certification` stays false.

`FieldAddArithmetic.reduced_add` supplies a shared pure integer reduction lemma.
It requires the input bounds and three carry/borrow reconstruction equations
as premises. Its closed proof and kernel check do not establish those equations
for a native field body by itself.

## Go field addition

```sh
python3 decaf_generate.py
python3 decaf_go_field_proof.py
python3 -m unittest discover -s tests -p test_decaf_go_field_proof.py
```

The field replay binds Fq/Fr Go64 sources to the generation receipt, freshly
extracts the package and pinned `math/bits`, and checks `GoFieldAdd.add_correct`
and `GoFrFieldAdd.add_correct`. For every canonical input pair, the result is
canonical and equals addition modulo the respective Fq or Fr modulus.
`GoFieldAliases` and `GoFrFieldAliases` supply Fq and Fr disjoint-output, left-output, right-output,
equal-input and all-equal corollaries. Inputs are read before exclusive output
ownership is recovered for the writes; the applicable corollaries preserve the
other input. Sixteen theorem roots require closed global assumptions and a kernel
recheck.

Each theorem explicitly exposes three helper resolver equations and the
respective `FqUint1` or `FrUint1` underlying-type contract, in addition to Perennial's semantics, heap
and FFI contracts. Empty global assumptions do not establish a concrete
interpretation satisfying these premises. The native entry-point resolver,
full semantics consistency and compiler/extraction correspondence remain
separate obligations.

Separate Fq and Fr modulus mutations must each fail their named native boundary
witness and arithmetic proof after fresh successful extraction and helper compilation. Native tests
also cover same-array aliases and a one-word offset overlap in a larger backing
array for both fields, preserving untouched cells. General offset-overlap
refinement remains open. Evidence is generated atomically under
`.work/decaf-go-field-proof-replay`; `full_certification` remains false.

## Rust field addition

```sh
python3 decaf_generate.py
python3 decaf_field_proof.py
```

The field runner requires the fresh source-bound Fiat import build described
above. It consumes the source bound to the generation receipt and
extracts Fq addition with its native helpers. `RustFieldAdd.v` proves canonical
output limbs, output length, and addition modulo Fq for every canonical input.
`RustMultiply.v`, `RustBorrow.v`, `Carry.v` and `RustSelect.v` prove the helper
arithmetic and its operation bounds. The finite-word model includes signed
casts and arithmetic shifts; `usize` is 64 bits.

The extracted body must match the proved sequence of 16 array reads and eight
writes and the reviewed helper-call inventory. `RustArray.v` proves bounds and
length preservation across writes. Safe Rust borrowing supplies distinct output
and input references. Changed operation structure requires renewing the safety
composition, even if an output-equality theorem still checks.

The original, wrong-modulus, wrong-multiplication and wrong-row-carry cases are extracted
and compiled independently. The modulus mutant must fail the native boundary
witness and the field arithmetic theorem. The multiplication mutant adds one
to the native helper's product and must fail both the Rust zero-product test
and the concrete Rocq `multiply_zero_witness`; this control does not replace
the universal multiplication-helper theorem. The row-carry mutant rewires one
operand while preserving the helper/read inventory; it must fail a native
Montgomery-product witness and the universal first-row arithmetic theorem.
All 33 theorem roots require a
closed global assumption set and a recursive VM-free kernel recheck. Evidence is generated atomically under
`.work/decaf-field-proof-replay`.
The replay binds resolved hax, Rust compiler/Cargo/rustdoc/driver and Rocq
compiler/checker artifacts. It rechecks those artifacts, compiled proof imports,
source copies, extraction bytes and build receipts before accepting the result.
`RustMultiplyWords.v` checks the full multiplication body's output-word
canonicality, output length and bounded array-access interface. The runner binds
that interface to all 72 reads, eight writes and the exact operation inventory.
The multiplication body's field arithmetic correctness remains a separate
theorem obligation.
Output-word canonicality uses the total modular `Core` model and does not prove
absence of native overflow. The access connection is a checked source inventory,
not yet a kernel theorem about the complete native operation/dependency graph.

`RustFiatPrimitives.v` supplies the next bridge pieces: native Rust32 multiply,
carry, borrow and selection helpers agree with Fiat's interpreted primitives and
their output casts. Its additional product-high bound justifies adding a one-bit
carry without u32 overflow; the two-carry inline addition is covered separately.
These lemmas concern the extracted helpers under the supplied `Core` semantics.
They do not yet compose the complete multiplication body, establish its array
access safety, or discharge extraction/native-semantics correspondence.

`decaf_native_prefix.py` derives multiplication checkpoints from the actual Hax
body. `RustMultiplyRow.v` proves the first schoolbook row's integer value, length,
canonical words and decomposition of the native multiplication into that row
and its remainder. `RustFirstReduction.v` connects the first Montgomery reduction
to the remaining native body and proves its integer recurrence, including the
reduction coefficient and discarded low word. The generated checkpoint sources
and their compiled imports are included in replay freshness checks.

These prefix results leave seven multiplication/reduction rounds and final
canonical reduction open. The intended full Fiat bridge is semantic equality of
the complete canonical output lists: independently prove native and exact-option
Fiat correctness, then use canonical radix-digit uniqueness. This avoids requiring
syntactically matching intermediate programs; it does not replace native safety,
termination, compiler or trace proofs. The earlier experimental row-to-Fiat
equality did not complete kernel checking and is not evidence.

## Orbis nonce refinement

[`nonce-contracts.md`](nonce-contracts.md) records the exact-source obligations
for the responder's stored nonces and the initiator's local nonces. It covers
consumption, cancellation, context checks, request-ID reuse and the distinction
between insertion identity and scalar freshness. These are source-reviewed
contracts; native refinement and protocol security proofs remain open.
