# PR160 reduced Transfer slice: results and handoff

Runtime: **844389ee069e1fb2e576708842d0b389b4d9a44a**. This is a development-only
result handoff from the original qualified local checkout, not certification of
this draft's changed source tree. Three reduced milestones completed locally:
actual matched spike and independent reviews; direct-Lean decision; ordered64
projection and canonical permanent-spend field gates with fail-closed CLI evidence
publication. Broader family/system/state/release gates remain open.

## Why direct Lean

The compared property is the same four equations over seven field values:
boolean selector, selected nullifier, selected root, and dummy-input zero amount.
Clean used four actual circuit assertions, local length zero, arbitrary environment
and offset, soundness/completeness and no new wires. Direct Lean proves the same
field property and constructive completion with fewer interface declarations.
Both reuse the shared Contract algebra; these are not independent algebraic proofs.

The retained source files are in `comparison-sources/`, as review snapshots outside
the active Lean package. They require their original Lean 4.33.1/Clean dependencies;
no second package or downloaded dependencies are shipped here. Contract is 75
physical lines (64 nonempty), Direct 27 (19), Native 103 (87), Controls 106 (88).
The existing canonical package uses Lean 4.30.0. Adopting Clean would add interface
and migration maintenance while leaving the runtime compiler/row correspondence
obligation intact. The manager adopted direct Lean on that coverage/maintenance
basis after actual Claude Code Opus5.5 and independent critical review.

Observed seconds, with setup and audits separated:

| Case | Target compile | Audit | Whole owned worker |
| --- | ---: | ---: | ---: |
| Shared Contract | 67.411888 | 2.031310 | 151.797066 |
| Direct | 98.584186 | 2.030550 | 226.195555 |
| Native Clean | 97.592175 | 2.531629 | 251.390597 |
| Controls | 97.590647 | 2.534537 | 251.825584 |

These are observations, **not like-for-like proof speed**. The audits cover
2 Contract, 4 Direct, 8 Native and 7 Controls theorems plus five instances; reached
dependency closures and uncontrolled OS caches differ. Dependency preparation is
separate. Our package-first provider-layout and legacy artifact-role defects caused
two failed setup attempts; neither was a theorem failure, semantic control, or
intrinsic Clean cost. Source LOC excludes that infrastructure debugging effort;
no author-hour estimate is asserted.

## What the final canonical result establishes

`TransferStatement.lean` gives the independent semantic 64-field record and its
list injectivity. `statement_projection.py` checks the closed Rust AST export's
complete ordered path list and generates `RuntimeTransferStatement.lean`.
The exact retained export and generated source are included, unchanged, for
review and byte-for-byte generator reproduction. Rust AST interpretation remains
a translation assumption, not a Rust refinement or cryptographic proof.

`SpendGateInputs.lean` defines Square, Linear and evaluation; `PermanentSpend.lean`
proves exactly five canonical interfaces: `branch_sound`, `branch_gates_complete`,
`assignment_branch_sound`, `required_input_real`, `required_assignment_real`.
The audit also checks Boolean and two arithmetic helpers (eight total) and four
definitions. Proofs have finite heartbeats and explicit arbitrary-Field/environment
premises. The required empty selector is constructed; its zero evaluation is a
conclusion. Direct evaluated nullifier/root equalities remain explicit premises.
Applying the LC assignment theorem to actual runtime rows separately requires
source/row correspondence. Computed roots can be general deferred-square
expressions; no claim makes every runtime expression linear.

The F17 controls are semantic field-gate tests joined by reviewed source
correspondence, not newly executed canonical runtime mutations. AST evidence
contains six intended extractor refusals, one adapter helper-coordinate rejection,
and four field/order mapping refusals. A compiler error or timeout is never a
successful negative control. Full Transfer, range/volume replay, hash/Merkle,
caller/verification-key semantics and permanent-state uniqueness/replay/atomicity/
durability are not closed. Historical nullifier generation/history windows are
excluded. Commonware trust covers unmodified upstream only; Shieldd local patches require their own qualification and do not inherit upstream proof.

## Retained identities and evidence availability

All SHA256 identities below identify **retained local artifacts**, not remote
certificates or independent semantic correspondence. Full raw captures, provider
inventories, qualifications and historical receipt are ignored `.work` artifacts
and are not shipped. No generated evidence was hand edited. The draft's register
preregisters the historical authority but leaves its new receipt SHA null; it
cannot promote until the exact qualified inputs are available and current source
inputs are validated through the existing atomic `write_result` commit point.
Only the two derived link pointers are normalized; substantive inputs are not.

| Artifact | Retained SHA256 |
| --- | --- |
| Comparison descriptor | d080f819e5a8f6c672f30ccb103d88bfbcf28bd4d7424022eef91f3e3ab558a5 |
| Direct-Lean decision | 0cc27eb8b33865817b64842f1c1d0c8d4f419811a562fe647a3056557dd4555d |
| Contract audit DATA | d4411a133e37c478244c5da13d539400efbabd2e76e38a772e3da19bc652ded0 |
| Direct audit DATA | 1c855b7177c5aec087ac4cc7c5faf7ae38d087b6e3215b50613d521d9b7e23ac |
| Native audit DATA | 35fc9d776e5906c1b68f6418de1d7ba4b7ff0321f19599157abb94323410b1b5 |
| F17 Controls DATA | 4a3b5969d5d797b40968b136448e70f65b19dac230ace7512b5ffd472e90f6cf |
| Ordered64 projection DATA | 739573fe2ce3b43c72d8f62c244b94c353767f82db39aabc446b08264e9a34ce |
| Canonical audit DATA | 1674535be6c565e96be3a43d1d58c3d063362603c00582b2919513c8f85edce2 |
| Six-role qualification authority | 19ff897c3ee4f109b4e76b12cc54caf9c3a5f7421a218d6fc90e19d12f2aae11 |
| Original local receipt | 28cbf12012f0b866f8e58a216840925c23c7190f73d47892fba82e5261798911 |
| Final actual Opus review DATA | b917cce8cc144499bd6a6e7058454abf53c2b1e55f5826d4a795f2a32a7876f3 |

The original local qualification used compiler/kernel, cache/OS, retained-core and
external IR preservation assumptions, source-reading bridges, and current raw
identity checks. Pretty-printer abbreviations were not unabridged proof-term
review. Final Opus reported 37 turns against requested35; this provider/controller
seam was disclosed, **not turn-limit compliance**. Time/memory/typed closure and
the substantive APPROVE were independently reviewed. Some review coverage relies
explicitly on previous full formal audits rather than repeating their expansions.

## Main-based delivery and reproducibility

The first commit replaces the retired main stacks with the exact compact foundation
previously proposed in closed draft #7 (which remains closed). It is a substantial
retirement, preserved in Git history, not a tiny diff. Subsequent commits add this
reduced slice only. Unrelated unfinished working-tree campaigns, caches, toolchains,
composed runtime workspaces and raw logs are excluded.

A fresh checkout can run light unit/policy tests and reproduce the included
export-to-generated-source equality. With the pinned dependencies, named Lean
modules and `PermanentSpendAudit.lean` expose the exact mathematical interfaces
for a fresh supervised audit. Re-running the Rust extractor additionally needs
the clean locked runtime and Rust dependencies. Neither route by itself supplies
the omitted qualified receipts/provider observations. The narrow CLI intentionally
refuses missing authority, changed/null pins, replaced receipts, altered substantive
inputs, and byte-mismatched generated sources; post-link checking is linkage-only
with an independently retained expected receipt SHA.

Automatic PR CI is light testing only. The inherited broader manual pilot workflow
is not the scoped local proof replay or portable certification and requires a
separately supervised, current-pin validation. The changed PR formal-source digest
must not be described as the original dirty checkout's qualified receipt inputs.

Draft preparation validation: Python 3.13 ran 29 light tests with exit0 (one Windows POSIX process-group skip), and `security.py check` passed. These tests use synthetic authority/receipt fixtures where required; they are not new proof evidence. The policy route was adjusted to avoid requiring an unshipped historical inventory script. No Lean, Cargo, model-checking or runtime proof job was replayed for publication.
