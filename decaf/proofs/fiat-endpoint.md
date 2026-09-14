# Exact Rust Fq / Fiat endpoint

```sh
python3 decaf_field_proof.py
python3 decaf_native_fiat_bridge.py
```

These commands require the pinned toolchains, generation receipt and fresh Fiat
source-build receipt described in [README.md](README.md). Run one heavy replay
at a time. The bridge requires the complete current 64-root native receipt and
all seven negative controls. It recompiles the exact-option `FiatMultiply.v`
and checks 24 roots: eight typed-pipeline roots and 16 endpoint lemmas.

`NativeFiatEndpoint.exact_fiat_multiplication` equates the entire canonical
output list of extracted Rust `fq_mul` with the interpreted exact Rust32 Fiat
pipeline body. Both inputs must contain eight canonical u32 words and represent
values below Fq's modulus. The initial output list has length eight.

Fiat's multiplication specification compares decoded values. `FiatEndpoint.v`
derives its concrete Montgomery decoding equation; `MontgomeryBridge.v` proves
the modular cancellation steps. `FiatRepresentation.v` connects the native
little-endian Horner value to Fiat's positional value and canonical partition
predicate. An explicit one-word inverse identity establishes invertibility;
this cancellation does not require an additional primality assumption.

The bridge remains a theorem in the supplied `Core` semantics. It does not
establish native overflow/panic safety, extraction semantics, termination,
other fields or languages, group/encoding correctness, compiled traces, or
consumer and protocol refinements. It is not a general printer-correctness
theorem. `full_certification` remains false.

The native arithmetic replay checks its roots recursively without VM reduction.
The separate Fiat endpoint replay uses recursive kernel checking with VM
reduction enabled and explicitly retains Fiat's Rocq VM/compiler trust.
Every audited theorem must have a closed transitive global assumption set.
Source-build libraries, proof plugins, installed Rocq/OCaml and standard
libraries, and the trusted extraction boundary remain as documented in the
underlying toolchain receipts.

Before and after checking, the runner verifies source, generation, matrix,
native receipt, compiler, copied proof and compiled-artifact identities. Missing
input hashes or RecordUpdate imports fail validation. A changed native receipt
or source requires renewed native replay before the bridge can pass. Reports
are refreshed atomically under `.work/decaf-native-fiat-bridge`; failed and
interrupted runs cannot retain a prior successful status. Logs retain the
100 MiB cap, and proof artifacts have a separate 1 GiB acceptance bound checked
at command boundaries.
