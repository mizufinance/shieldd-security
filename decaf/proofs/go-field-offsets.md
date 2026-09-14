# Go addition and overlapping windows

`decaf_go_field_proof.py` replays Fq and Fr addition on a Linux x86-64
proof/native-witness host. This is not native ARM64 execution evidence.

The 27 roots include the existing addition and equal-pointer corollaries,
three array-resource lemmas, and four offset corollaries per field. Their
list decompositions place each four-word window within its backing array.
They cover all five ways three windows can share backing storage:

- All three share one backing array.
- Both inputs share one backing array and output is separate.
- Output and left input share one backing array.
- Output and right input share one backing array.
- The three windows are disjoint, using the existing disjoint corollary.

Shared reads borrow fractional ownership and restore it before any output
write. The output accessor then restores the entire backing array with exactly
the four-word output window replaced. Separate operands and all words outside
the output window are preserved. The statements permit arbitrary prefix and
suffix lengths, rather than enumerate a finite set of offsets.

The proofs are conditional partial weakest-precondition theorems in the
supplied Go semantics. They still require a concrete semantics/resolver model,
a native allocation and pointer interpretation, and termination proofs.
Closed transitive assumptions do not establish that those semantic contracts
are inhabited. These corollaries do not classify concrete Go allocations.

The native fixture covers 343 offset triples for each field with three input
patterns: 2,058 cases. It snapshots the inputs before the call and compares the
entire backing array against the expected modular sum and unchanged frame.
The fixture checks reduced inputs explicitly and includes carry/reduction cases.
These tests are regression and mutation witnesses, not universal proofs.

The replay requires the exact generation recipe and adopted source identities,
plus `decaf_perennial_build.py`'s fresh source-build receipt. It binds the
consumer-selected Go runtime, package-loader dispatch, Goose binary, resolved
Rocq compiler/checker, standard-library sources, copied proofs, extraction,
compiled artifacts, and audit. It checks identities before and after recursive
kernel replay and again before atomic acceptance. The checker uses bytecode
reduction with explicit Rocq VM/compiler trust.

Two modulus mutations must fail their native boundary witness and arithmetic
theorem. Two early-output-write mutations must fail a native offset/frame
witness and the exact first-call execution-order proof site. The runner keeps
these rejection stages distinct. Missing imports, wrong error sites, duplicate
errors, changed generation options, interruptions, and timeouts cannot satisfy
the controls. `full_certification` remains false.
