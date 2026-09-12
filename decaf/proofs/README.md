# Source-linked Decaf proofs

The shared specification uses Rocq. Native field generation uses the pinned
Fiat-Crypto source; Rust and Go retain native implementations. Proof extraction
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
opam switch with OCaml 5.3.0, Rocq runtime 9.1.1 and standard library 9.1.0.
It requires the pinned `record_update` checkout at `.cache/record-update`.
Other host artifacts need their own reviewed identities before use.

For full field extraction, generate arrays without field-element typedefs.
Unsupported extraction and unproved primitive semantics must be resolved in the
source/generator or the dedicated semantic support, never by editing generated
proof output or importing hax's dummy core library.
