# Transfer proof remaining work inventory

As of 12 October 2026, the full Transfer proof remains open. There are three required results: arbitrary-assignment circuit soundness, total construction for independently legal inputs, and the consequence of actual pinned runtime admission and execution. Numerous reviewed component proofs support these results, but none of the three concrete final proving declarations is recorded as complete.

This inventory describes the active Pari and direct Lean campaign. The older gnark and Decaf checkout opened by this chat is not its build baseline. Historical handoffs remain intact; their old counts and running-state observations must not override newer sources and receipts.

## Exact baseline

| Item | Verified baseline |
| --- | --- |
| Mac publication checkout | `/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/shared-build-handoff` |
| Security HEAD before these planning documents | `a74842d5e25ab999ba4c0e34825ad74c114e8a38`, clean, branch `codex/security-assurance` |
| Runtime lock | `844389ee069e1fb2e576708842d0b389b4d9a44a` |
| Runtime snapshot | `work/runtime-snapshot` under the campaign root; observed clean at the locked SHA |
| Lean | `leanprover/lean4:v4.30.0`; retain the exact accepted Lake manifest and Mathlib identity |
| Relation | 200,770 stored rows: 177,954 arithmetic rows and 22,816 assertion/link rows; declared domain 262,144 |
| Inputs and observables | 22,735 original input columns; ordered 64 public fields; statement hash; committed blinding |
| Latest source selections | `mac-source-closure2636.json` and `merged-scalar-predicates3281.json` in the existing source integration directory; source-only selections, combined kernel replay UNRUN |
| Latest retained desktop ancestry | 216 modules and 1,547 reports in the coordinator record; these are scoped report counts, not an implementation proof |
| Local process census | No active proof compiler observed during this inventory |

The starting checkout `/Users/antoinecyr/Documents/Source/shieldd-security` instead has security HEAD `5503ed78` and runtime lock `5aa0dbd7632257831b345c296458861c52a81b33`. Do not build or certify Transfer from that baseline by accident. Current development in `/Users/antoinecyr/Documents/Source/shieldd` is also a different runtime revision.

## Desktop reconciliation

The read-only inventory from **Wait for transfer proof instructions** found the maintained work at `C:\src\shieldd-formal`, with newer packets under `.work\diagnostics`. Its formal HEAD is `b0f7e8b885dc0c13ee3bd5c82851afb690f48d48`, with 16 tracked modifications and 1,178 untracked entries. Its publication checkout is clean at `cec1b30defc23497c8e9b30528dca12b09d328ea`; its cached shared branch stops at `22efb9ec8d4d62a50e62393c74bad660bf89e856`. Mac HEAD `a74842d5...` is absent from that local Git object database. All three formal views lock the campaign runtime `844389ee...`, and `C:\src\shieldd-pr160-844389ee` is clean at that full SHA.

Newer desktop compiler-success packets require original transport and independent reconciliation before inclusion in the reviewed Mac closure:

| Packet | Fresh complete reports | Recorded seconds | Peak RSS MiB | Olean bytes |
| --- | --- | --- | --- | --- |
| Scalar pack chunk | 10 | 7.27 | 785 | 85,088 |
| Scalar pack walk | 7 | 7.30 | 799 | 202,736 |
| Policy prehash fields | 6 | 7.06 | 743 | 59,080 |

The policy packet inherits 217 modules and 1,557 reports, then adds one module and six reports. These newer counts do not imply native execution or final proof closure. Pack-walk attempt 05 failed on a `List.take`/`List.drop` rewrite; policy attempt 01 failed on an unreduced lambda. Both have successful successors and retained zero-credit failures.

The two latest portable archive candidates are `transfer-scalar-pack-walk-endpoint-20261012-06/portable-windows-scalar-pack-walk-endpoint01.tar.xz` and `transfer-policy-prehash-fields-endpoint-20261012-02/portable-windows-policy-prehash-fields-endpoint01.tar.xz` under the desktop diagnostics directory. Resolve their complete exact ancestry, including pack-chunk, rather than importing only final source files.

The native three-control group remains UNRUN. Its most recent attempted launch stopped before any test because a CRLF shell script produced `set: -<CR>: invalid option`. The prepared `transfer-state-controls-successor-20261012-02` generator writes explicit LF bytes; its review records unchanged assertions and budgets, and its fresh output namespace is absent. The intended controls exercise delayed Ordinary volume rechecking/child discard, Host queue-fault retry publishing effects without an index, and rollback followed by genuine replay/index publication. Artificial queue-fault reachability remains an explicit limit.

The prepared native group has a 7,200-second bound, one worker, 4 GiB memory and 8 GiB swap cgroup limits. Those are native-job settings, distinct from the Lean module guards. The desktop observed about 6.33 GiB free physical RAM, no verification processes and no running WSL distribution. Recheck admission at launch; this observation does not authorize bypassing a guard.

## Reviewed work to reuse

- All 177,954 arithmetic rows have a reviewed constructor, framing and uniqueness proof, supplied by 599 leaves, ten balanced groups and a root. Do not regenerate or rerun them merely to recover a decoded copy.
- The complete indexed assertion/link provider covers all 22,816 positions. Equivalence to recorded polynomials and row coverage are established; legal-input truth for every polynomial is a separate obligation.
- Full relation fixed-point recovery and the public, committed and constant-copy links are established. In `CapturedFullRelation58`, these are `rho 1 = rho 22737`, `rho 2 = rho 9`, and `rho copy = rho 0`.
- Reviewed captured registry and full 16-level field Merkle path/anchor work exists. Candidate path construction covers 9,506 field arithmetic rows on the same original inputs. Concrete natural, canonical and SDK interpretation still requires instantiation.
- Actual concrete curve model, base order, curve cardinality, global exponent and cofactor capstones already exist. The abandoned Hasse port is not a prerequisite for completing Transfer.
- `LegalSharedRows271.legal_completed` puts arithmetic, selected 10,783 Boolean positions, 66 word entries, four subgroup families and anchor row 178117 on one assignment. It still has explicit representation, legality, bounds, coherence and seed-meaning premises.
- `LegalAliasMeanings276` derives the three normalized alias seed meanings. `LegalWordValueData278` partitions word values into those aliases or 53 other distinct columns. The actual Boolean exclusion instances and remaining seed meanings are open.
- Desktop source models cover substantial finite-word arithmetic, canonical field encoding, scalar operations and represented program evaluation, plus admission, delivery, nullifier/SCT/cache/finalization models. Their exact scope remains modeled source behavior; native whole-trace correspondence is open.
- Retained runtime tests and genuine branch proof receipts provide scoped execution evidence. They do not replace arbitrary-assignment soundness, universal construction or native refinement.

The old count of 1,467 constructor assertions and its 21,349-row remainder describe an earlier assignment. Do not report that remainder as current. Likewise, do not add Boolean, word, subgroup and earlier assertion counts: they overlap and may refer to different assignments. Compute any current remainder as an exact set difference tied to one constructor.

## Outstanding circuit and construction obligations

| ID | Remaining work | Completion evidence | Build owner |
| --- | --- | --- | --- |
| C1 | Instantiate the mathematical field and scalar interpretation, canonical representation, curve model, generators, cofactor/subgroup mapping and Poseidon domains, arities, IVs and schedules | A concrete `TransferSem.Crypto` with required laws derived from accepted capstones and exact parameter sources; no desired semantic conclusion as a premise | Mac, using desktop codec results |
| C2 | Interpret every remaining captured node, column and consumer independently | Arbitrary full satisfying `rho` yields the actual source algorithm meanings using fixed-point and indexed row certificates | Mac |
| C3 | Complete all semantic components | Concrete joins for registry, sender and receiver user paths, authorization, both spend branches, both outputs/recovery, volume, routing, encryption and signed balance; all on the same witness | Mac |
| C4 | Close exact public, committed and padding interpretation | Exact ordered public64 and statement transcript, same bounded blinding/opening, and equivalence to the verifier's actual padded relation | Mac; desktop supplies verifier binding |
| C5 | Produce full circuit soundness | A concrete theorem deriving `TransferFullCarrierAcceptance.LocalRowSoundness`; that predicate cannot remain a premise of its own proving theorem | Mac |
| W1 | Derive a compatible original input seed | Encode the independent legal witness into all 22,735 inputs; derive private/hint/alias meanings, three parity relations, word bounds, and the 58 actual Boolean exclusion instances; preserve declared observables | Mac |
| W2 | Derive every assertion/link truth | Exact coverage of all 22,816 assertion/link positions on one constructed assignment, including still-unjoined ranges, exclusions, equalities and branches | Mac |
| W3 | Prove frames across every seed stage | Subgroup, Boolean, word, registry/path and subsequent seeds preserve each other's required values; any inactive auxiliary normalization preserves public64, statement and blinding | Mac |
| W4 | Produce total legal-input completeness | Compose `TransferSemanticConstruction.constructed_transfer_semantics`, the concrete seed and `CapturedFullRelation58.candidate_full_iff` without a supplied `TruthAt` conclusion; include all stored rows and padding | Mac |

Immediate repair work is narrow. The actual avoidance check after the accepted alias/value modules hit the heap limit; partition it into small index or interval certificates and compose. The last Mac interruption record also retains a `FieldPrimeNode38` compiler-success stream rejected for an unused simp argument. Its accepted prefix does not qualify the rejected final source. Inspect its exact receipt and maintained generator, repair the warning, and rerun only the changed target if it is still needed. Retain all failures.

## Outstanding native obligations

| ID | Remaining work | Completion evidence | Build owner |
| --- | --- | --- | --- |
| N1 | Bind represented arithmetic and codec models to reachable native values | Exact pinned field/scalar aliases, private constructor origins, bytes, indexing, Choice/CtOption behavior, operations and actual caller census; distinguish the BLS field Scalar used through Jubjub Fq from the subgroup scalar order | Desktop |
| N2 | Bind real proof admission and action projection | Exact proof mode, key/relation registry, envelope bytes, current context, canonical public64, committed opening and authorization; cover mixed-family and fee locations that affect Transfer | Desktop |
| N3 | Refine actual transaction execution | Concrete collections, getters, Clone/COW, ownership, callbacks, source ordering, nullifier freshness, volume and SCT writes, parent/child cache effects and savepoint behavior | Desktop |
| N4 | Refine finalization and publication | Actual source-ordered flush, SCT seal, state transfer and Host publication; bind the corrected finalizer/driver models and all reachable branches | Desktop |
| N5 | Prove recovery under the declared environment | Actual Commonware/NOMT patches, locks, poison/owner/partition behavior, snapshots/ICS23, crash and error propagation, close/reopen/readback, and exact permitted OS primitive assumptions | Desktop |
| N6 | Run the three prepared native controls | Fresh admitted executions with intended semantic observations and complete receipts. Currently compiled UNRUN; an admission refusal or timeout is not a negative control result | Desktop |
| N7 | Produce the implementation consequence | Actual pinned accepted/delivered traces refine the completed circuit and execution specifications; no supplied final poststate or broad native-correspondence premise | Desktop with C5 |

N1 through N7 are the largest unresolved scope risk. More proved model operations are useful only when they discharge a specific reachable native interface. Source hashes authenticate identity; they do not prove the execution/model correspondence.

## Final integration obligations

| ID | Remaining work | Pass condition |
| --- | --- | --- |
| F1 | Reconcile both physical machines | Same exact source selections and runtime lock; preserve desktop unpublished work before any update; no old process or duplicate controller |
| F2 | Select the final dependency closure | One exact source identity per selected module, explicit variant decisions, acyclic imports, portable generators/data and accepted ancestors; historical variants remain outside the active closure |
| F3 | Review all three endpoint contracts | Full types, premises, all public/private/generated declarations and axioms; reject `sorryAx`, admitted statements and hidden desired conclusions |
| F4 | Validate semantic controls | Altered coefficients/columns/assertions/roles, range and canonical boundaries, selector polarity, public/committed links, replay/nullifiers, failure rollback and recovery. Observe the intended semantic failure |
| F5 | Add an actual full Transfer CLI scope | Existing `security.py` offers only `legacy` and `transfer-slice`, and `check_register` requires every family blocked. Extend the existing CLI/register checks for a precisely qualified Transfer result without unblocking unrelated families or system release |
| F6 | Perform final guarded replay and atomic publication | Reproducible clean exact-lock input closure, named final roots, complete audit and receipts, atomic result/claim update, separate handwritten and generated commits where practical |

Keep proof-system knowledge, mode-specific batch knowledge, setup/transcript/opening and collision-resistance assumptions explicit. Keep the semantic-or-hash-collision branch. OS contracts may describe primitives, but cannot assume whole-store recovery or successful atomic publication.

## Sources

- [Historical completion plan](../transfer-20261009/completion-plan.md), especially Required result, the three endpoint contracts and latest reviewed checkpoints.
- [Generic final acceptance consumer](../../circuits/ShielddSecurity/TransferFullCarrierAcceptance.lean) and [independent semantic target](../../circuits/ShielddSecurity/TransferSem.lean).
- [Shared-assignment constructor](../transfer-20261009/sources/mac/legal-shared-rows271/source/ShielddSecurity/LegalSharedRows271.lean).
- Existing coordinator files under `/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/resumed-orchestration-20261009-01`: `full-transfer-endpoint-premise-ledger01.json`, `continuation-state-20261010-2300.json`, `external-assumption-boundary-review28.json`, and `provider-authentication-interruption450.json`.

This is an inventory and plan checkpoint. It adds no proof, runtime execution, replay or certification result.
