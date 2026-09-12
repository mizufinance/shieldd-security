# Source-linked Decaf proofs

The shared specification uses Rocq. Native field generation uses the pinned
Fiat-Crypto source with the checked-in array-index printer patch; Rust and Go
retain native implementations. Proof extraction
is a trusted translation boundary, with the exact executable identity recorded.
The implementation program is tracked by issues #2 and #4–#6.

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

## Go model obligations

The pinned Perennial/Goose revision needs fixed-array repairs before consumer
refinement: pointer-array indexing must preserve addresses, array stores must
read the corresponding element, signed bounds must reject negative indices,
and array allocation needs executable semantics. Its current array-allocation
rule uses `AngelicExit`, which admits arbitrary partial-correctness
postconditions. Go theorem acceptance therefore also requires return/progress
evidence excluding reachable placeholder exits. A closed axiom audit alone is
insufficient. The pinned array load/store proof instance also contains admissions
and must be completed before it can enter the theorem closure.

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

This is partial functional correctness. Termination, array allocation,
field/group/consumer refinement, and compiled leakage traces remain separate
obligations; `full_certification` stays false.

## Rust field addition

```sh
python3 decaf_generate.py
python3 decaf_field_proof.py
```

The field runner consumes the source bound to the generation receipt and
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

The original and wrong-modulus source cases are extracted and compiled
independently. The mutant must fail the native boundary witness and the field
arithmetic theorem. All 14 theorem roots require a closed global assumption set
and a kernel recheck. Evidence is under `.work/decaf-field-proof-replay`.
The generated full multiplication body is typechecked; its field arithmetic
correctness remains a separate theorem obligation.
