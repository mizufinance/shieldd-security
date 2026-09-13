# Candidate binary-analysis qualification

The original BINSEC source is pinned by `decaf/inputs.json`. The optional
`binsec-demand-decoding.patch` replaces eager successor decoding at one regular
code fetch site with on-demand decoding. It is a separately identified tool
candidate, not a change to the approved tool identity or an assumption that
unsupported instructions are safe.

Build the candidate from the exact pin in a separate source tree, apply the
patch, and use the release profile consistently for its executable and plugins:

```sh
OPAMROOTISOK=1 opam exec --switch=binsec-fv -- dune build -j2 -p binsec @install
python3 decaf_qualify.py --dune-root /absolute/candidate/tree --rust-fq-add
python3 decaf_flow_qualify.py --dune-root /absolute/candidate/tree
```

The first command runs in the candidate source tree. The runners run in the
formal repository. Candidate versions, executable/component hashes, source
patch identities, binary/configuration hashes and command logs are recorded.
Component inventories do not attest which dynamic libraries were loaded.

The extended runner compares both tools on the same x86-64 and ARM64 binaries.
It covers public indirect calls, returns, loops, reconvergent branches, delayed
branch/address leaks, and a store/load/call leak. Completed path counts,
endpoints and leak locations must agree on the supported fixtures. Depth and
timeout controls must be rejected as incomplete. Reached unsupported x86-64
floating-point and ARM64 undefined instructions must block analysis; the
on-demand candidate must complete when the guarded instruction is unreachable.
This does not establish floating-point instruction support.

All reports retain `qualification_complete: false` and
`full_certification: false`. These controls do not establish analyzer
equivalence, a verified lifter, complete runtime coverage, native ARM64
execution, or complete library/consumer constant-time properties. The strict
pilot classifier continues to reject lifter errors, incomplete exploration,
missing endpoints and ambiguous results.
