# Coverage and remaining assurance obligations

This inventory implements [issue #2](https://github.com/mizufinance/shieldd-security/issues/2).
It is a bounded review of named paths, not a repository-wide security audit.
Assumptions remain owned by the existing
[assumption ledger](../crates/core/component/compliance/formal/assumption-ledger.md).

## Revision and caller joins

Shieldd inspection revision: `b3de9fecebbaa8d44f5f582e3fae16287970300e`.
The circuit candidate remains `5aa0dbd7632257831b345c296458861c52a81b33` in
`shieldd.lock`. Neither is promoted by these library pilots.

| Consumer / entry point | Selected implementation at inspection | Secrets and residual boundary | Evidence status |
| --- | --- | --- | --- |
| Rust `crates/crypto/decaf377-ka/src/lib.rs`: `diversified_public`, `key_agreement` | Decaf `3cbab97f34d352b49bc1200dba839d37b223e66d` through the workspace patch | Secret scalar; arbitrary public peer point; subsequent `vartime_compress` | Uncovered: candidate library differs; generator-only pilot does not cover peer points or compression |
| Rust `crates/crypto/decaf377-frost`: signing commitments and responses | Same workspace Decaf patch | Hiding/binding nonces, signer shares, nonce lifecycle | Uncovered consumer join; library operator checks alone do not establish signing security |
| RDSA dependency `fc6045f0d9de5db8c37f57fa019e390367ba17cb` | Workspace Decaf patch; exact resolved features require consumer build closure | Signing nonce/key, scalar arithmetic and encoding | Uncovered construction and deployment boundary |
| Go `tools/gnark/internal/abi/statement_fields.go`: `ScalarMulNative` callers | `decaf377-go v0.2.0` | Private amounts/blindings, native conversions, intermediate points | Uncovered: old helper and `big.Int` boundaries; candidate removes this helper |
| Orbis FROST/PRE | Reported Rust `decaf377 v0.10.1`; deployed commit/lock not supplied | Signing nonces, PRE secrets | Unassessed deployment identity; no claim that updating Shieldd updates Orbis |

The pilot default Rust backend and normal Go build are compiled-analysis targets.
Other Rust feature combinations and Go `purego` receive functional checks only.
ARM64, minimal-backend compiled traces, arbitrary/secret point multiplication,
normalization/encoding pipelines, and consumer binaries need separate evidence.

## Prioritized gap inventory

Ownership names identify engineering roles, not an assignment to an individual.
Each closure requires evidence for exact source/build identities.

| Area / priority | Existing evidence and production path | Remaining property and closure criterion | Owner |
| --- | --- | --- | --- |
| Leakage and secret handling / P1 | This pilot; signing, key agreement and native witnesses above | Join migrated callers to analyzed paths, cover conversions and secret-derived points, then assess erasure/logging; distinguish modeled traces from physical leakage | Crypto/runtime security |
| Native primitive correctness / P1 | Library algebraic tests, independent Go affine oracle, Rust-produced wire vectors; circuit Decaf relations | Prove or independently check native field reduction, group/encoding validity and abstract-to-native correspondence; track randomized tests separately from proofs | Crypto/FV |
| Construction security and randomness / P1 | Compliance computational assumptions in the ledger; FROST/RDSA/KA and PRE entry points | Map exact transcripts, domains, nonce generation, zero rejection, RNG assumptions and key validation to protocol arguments for the shipped variants | Protocol/crypto |
| Stateful and concurrent behavior / P1 | Circuit transition semantics; runtime handling is explicitly separate in `docs/soundness/fv.md` | Model nonce use through retries, cancellation, crashes and concurrency; require executable duplicate-use/replay regressions and a reviewed state model | Signing/custody runtime |
| Parsing and native safety / P2 | Focused decoder F* checks and bounded fuzzing described in the root README | Inventory uncovered Decaf decoding, subgroup/identity checks, FFI, error paths and resource bounds; extend targeted fuzz/model checks where justified | Runtime/security |
| Deployment/proof correspondence / P1 | Exact `shieldd.lock`, focused reports, candidate/full-certification separation | Require an exact consumer/library/feature/toolchain join; compiler and target changes require rerun; setup provenance and runtime assumptions remain ledger obligations | Release/FV |
| Availability and operational trust / P2 | Ledger records external computational/operational assumptions | Name liveness, entropy, setup-secret erasure, physical/fault assumptions and responsible operational evidence; no claim that circuit proofs discharge them | Operations/protocol security |

Runtime dependency migrations belong in owning repositories. Circuit pin refresh,
complete proofs for every gap, and full-system certification are separate work.
