# Bankd integration boundary

Current target (2026-10-01): `shieldd.lock` pins Shieldd PR160
`844389ee069e1fb2e576708842d0b389b4d9a44a`. The Bankd observations and dirty
runtime replay snapshots below are historical joins; they do not establish a
current PR160 Bankd integration or certify its seven live proof families and
permanent-nullifier state. A fresh exact Bankd/runtime join and replay remain
open. No companion repository pin or generated evidence is changed here.

This maps implementation and scoped runtime diagnostics. The execution model
and Rust replay in this directory do not establish end-to-end Bankd settlement.

Read-only source inspection on 2026-09-29 identified Bankd main at
`d85ef61a29383894d18014b4dc2ae2ebfa67a026`. Its `shieldd` gitlink is
`c1aca125130281cf4816710c5b64d19b29db0313`, not this campaign's runtime candidate.
Before qualification, pin the Bankd candidate and the exact Shieldd gitlink,
build its real embedded library and builders, and record both identities. No
Bankd source was changed or executed during the initial inspection. A local
candidate now exists at `.work/bankd-current` on that base. Exact dirty Bankd
source `694886fafce11f761c29592a611020192a1ac992a1e7ca8eabdf2093496f8582`
passed `TestPerActionTransferConflictAndDurableEffects`: two genuine proofs,
one accepted transaction, exact replay and a distinct conflicting transaction
rejected, durable private effects observed and the real Shieldd database reopened.
Bankd itself uses an in-memory database in that alignment scenario.
`TestGenuineTransferJointCommitRecovery` passed all three named cases against
real persistent stores and genuine Transfer proofs. `before_commit` and
`before_publication` demonstrate two positive verified recovery/publication
paths. `after_commit` demonstrates refusal of same-height state with a stale
record and preservation of the previous record; it is not automatic recovery.
These inject failures at actual call boundaries, not process-kill or power-loss
faults. Exact logs, source/build identities and cleanup checks are retained in
`.work/diagnostics/bankd-header-header-694886fa-896000f2-20260929-01`.
Independent result review accepted this bounded scope; certification remains open.
The selected runtime base is `90428db824c17a61a94cadede1a1a49602700b6b` plus
reviewed observation/replay changes, pending a clean candidate commit. Preserve
the accepted per-action authorization design from Shieldd PR157; advance the
Bankd consumer rather than restoring the old per-input format. Generated Go
protos, native library, builders, keys and application/wallet state versions must
agree with that candidate. An unchanged C ABI does not establish wire, proof or
state compatibility, and no compatibility decoder is planned.

The stored compact-block header observer currently checks root width and exact
stored-byte identity. It does not independently derive the SCT block root from
the ordered commitments. A required follow-up must replay the actual SDK TCT
block finalization and compare that block root with the stored compact header;
the application state root is a different value. This correspondence remains
open even though the alignment and recovery tests above passed.

## Actual joins and reusable work

All links below refer to that inspected Bankd commit.

| Boundary | Existing implementation and required correspondence |
| --- | --- |
| Deposit | `x/shieldd/keeper/msg_server.go`, `deposit.go`, and `pending.go` join escrow with immediate or deferred Shieldd minting. Both deposit paths must allocate distinct canonical HostSource identities through the shared counter. Failure must not leave a debit without its corresponding note or pending claim. |
| Private Transfer | `MsgDeliverTx` passes the actual transaction bytes to the embedded client. Shieldd validates proofs/signatures and applies private effects. A pure Transfer must preserve Bankd escrow while its exact nullifiers, output positions/roots, signed bytes and indexes become durable together. A replay or conflicting spend must change neither ledger. |
| Withdrawal | [withdrawals.go](https://github.com/mizufinance/bankd/blob/d85ef61a29383894d18014b4dc2ae2ebfa67a026/x/shieldd/keeper/withdrawals.go) checks response count, destination and order, then releases per-denom escrow excluding pending deposits. Coin amount/denom correspondence additionally depends on the actual proof-bound Shieldd response, not merely the destination comparison. A post-execution error calls Shieldd rollback and makes Bankd EndBlock fatal. |
| Host execution | [host_execution.go](https://github.com/mizufinance/bankd/blob/d85ef61a29383894d18014b4dc2ae2ebfa67a026/x/shieldd/keeper/host_execution.go) uses a Cosmos cache for the ordered EVM batch. Success requires complete asset consumption. Revert or residual balance drops that cache and re-mints to the proof-bound refund address; failed refund aborts the block. The executor binds chain ID, transaction hash and withdrawal index. |
| Joint commit/publication | `ChainApp.Commit` in `app/app.go` orders BaseApp commit, Shieldd commit, recovery-record write, then `PublishCommitted`. `app/shieldd.go` publishes after restart only when Bankd height, Shieldd height/root and the independent record match. The older `x/shieldd/architecture.md` omits current recovery automation; implementation is authoritative. |
| Recovery | [shieldd_recovery.go](https://github.com/mizufinance/bankd/blob/d85ef61a29383894d18014b4dc2ae2ebfa67a026/app/shieldd_recovery.go) permits automatic rollback only when Bankd is one height ahead, Shieldd height is positive, previous-root binding matches, and record consistency checks pass. It rolls CometBFT back first, writes the verified record, rolls the multistore back, then re-reads and verifies alignment. Equal heights require a matching record; ambiguous state fails closed. |

Reuse Bankd's existing
[turnstile.qnt and specification](https://github.com/mizufinance/bankd/blob/d85ef61a29383894d18014b4dc2ae2ebfa67a026/x/shieldd/spec/turnstile.md).
It covers escrow minus pending deposits, per-denom conservation, no release
beyond minted backing, drain/refund exclusivity, and unique deposit sources.
Its reported results are simulations and scenarios, not an exhaustive or
cross-repository refinement proof. It deliberately abstracts the proof engine,
block abort/recovery and recipient policy. Do not duplicate this model here or
use its atomic actions as evidence that the two databases commit atomically.

## Next implementation and qualification obligations

1. Extend the real embedded tests in
   `shieldd_integration/shieldd_integration_test.go`, which already exercise
   deposit/spend and spent replay, host withdrawal, successful host execution,
   revert/refund, residual/refund, invalid deposit, and restart/commitment.
   Join the full private-effects observer to Bankd balances, publication height,
   actual committed transaction bytes and recovery record. Add distinct
   conflicting transactions, all enabled action families and shapes, fees,
   multi-action partial failure, and candidate abandonment; one repeated
   Transfer fixture is insufficient.
2. Connect the existing turnstile model to actual keeper operations and genuine
   embedded Shieldd results. Exercise same-transaction mixed deposit paths,
   cross-denom attempts, queued deposits, exact replay versus conflicting
   source reuse, wrong/reordered response effects, settlement failure, and
   refund failure. Require a specific semantic failure for each mutation and
   a restored positive run.
3. Compose real CGO execution with deterministic crash/failure boundaries before
   and after each commit, record and publication stage and during recovery.
   Reuse the case structure of `shieldd_integration/commit_order_test.go` and
   `tests/integration/shieldd_recovery_test.go`, but the latter currently uses a
   file-backed fake Shieldd. The new genuine joint-recovery case provides the
   narrow persistent-store composition described above, without qualifying every
   boundary or process crash. Compare both durable
   stores, Comet height, roots, record and published query snapshot after each
   restart, including a second interruption during rollback.
4. Keep process-crash recovery separate from power-loss durability.
   `app/shieldd_commit_record.go` syncs the temporary file and renames it; the
   inspected function does not sync the containing directory. Establish the
   filesystem/storage contract or strengthen it before claiming power-loss
   durability. Missing/stale records must remain a fail-closed outcome.
5. Revalidate the recipient-policy gap recorded by Bankd's
   `TestHostWithdrawalRecipientScreening`: the existing case uses a recording
   bank keeper, not an actual sanctioned compliance account. Decide and enforce
   the intended transfer/execution recipient policy through the real keeper;
   do not treat the historical test comment as a newly demonstrated exploit.

The existing native integration recipe requires Linux or Darwin, CGO, the
actual static library, matching builders and a compatible Pari registry.
The Bankd checkout is acquired and WSL access now works through the campaign's
execution operator. Earlier access-denied and Windows Quint launcher results
remain failed diagnostics, not qualification evidence. The selected candidate's
generated clients, native archive and builders have the scoped execution receipts
above. The broader consumer suite still requires its own matching composition
and genuine execution; an acquired checkout is not a completed settlement test.

The earlier failed allocation trace for instrumented builder source
`79434cbc4cd4186fcf23564cdf81274b9cb2554329f5575323bbd63d27136cf6`
keeps native/Bankd artifacts at their separately recorded identities. After all
nine registry checks, the first builder retained 3,257,764 KiB, then reached
5,736,168 KiB after the Transfer compile on another worker. It completed one
proof with 6,163,056 KiB high-water RSS; the second fixture stopped at witness
construction when system available memory fell below the original 1 GiB reserve.
The full test therefore did not pass. The proposed fixture-only change puts
unchanged registry loading and ordinary SDK building on the same blocking
worker. Allocator reuse is a hypothesis until the guarded comparison runs;
registry validation and cryptographic checks are not relaxed.
Joint atomicity here means consistent publication and verified recovery of the
two ledgers. It does not mean their physical database commits are simultaneous.
In particular, a failure after Shieldd persists but before the independent
record is written leaves equal ledger heights with a stale record. Current
startup and automatic recovery refuse this state. The operator must verify the
stores before using the existing `shieldd-rollback --bootstrap-record` path, or
restore/resync. A test of this refusal establishes that unverified state is not
published; it does not establish automatic recoverability or liveness.

The authored Bankd tests distinguish three scopes: real native Transfer
verification/effects with a Shieldd database reopen; persistent Bankd/Shieldd
commit-boundary failures and production recovery; and the existing separately
specified consensus/storage assumptions. The recovery tests seed Comet storage
from actual Bankd app hashes and inject errors around real calls, including the
post-rollback re-read. They do not execute a consensus network, kill a process,
interrupt an individual IAVL write, or simulate power loss. None is qualified
until the aligned native artifacts and generated clients are executed.

## Orbis remains an independent enablement gate

The proposed exact protocol and implementation stages are in
[orbis.md](orbis.md). They are under independent review and do not enable the
service. The proposed handler preserves fresh per-participant authorization;
it does not claim instantaneous global revocation or retractable shares.

The runtime's `deployments/orbis/images.lock.json` pins Orbis source
`0a0f935a85cc60e87561a9c7364fa80fdb3332df` and image
`sha256:e8b5a40d6b66f0da2f684c5624b9a9a2ac55c274d3b314ce6b7030f131612775`,
explicitly marked `decaf377`; startup rejects this incompatible deployment.
The required BLS12-381 PRE runtime, separate Jubjub release/PET capabilities,
ACP authorization, and real threshold corruption/release contract must be
identified and qualified before enablement. Current Shieldd documentation
explicitly marks production ACP policy enforcement, capsule-release/address-DH
APIs, private capsule location and Bankd seizure settlement incomplete.

Historical Tamarin sources under `reference/protocol` are requirements inputs.
They cannot certify an absent release service. In particular, a post-opening
owner proof does not establish pre-release secrecy: the service must authorize
the exact accepted capsule before disclosing its opening point.

### Existing Orbis behavior inspected

This distinction is based on code, not only the deployment README. At the exact
Orbis source revision above:

- [`bin/orbis-node/Cargo.toml`](https://github.com/sourcenetwork/orbis-rs/blob/0a0f935a85cc60e87561a9c7364fa80fdb3332df/bin/orbis-node/Cargo.toml)
  selects BLS12-381 and Vera authorization by default. Optional Decaf377 is a
  different build. The existing source can therefore support a BLS PRE target,
  but the pinned image's declared feature does not match it. The local
  `scripts/lib/common.sh::validate_orbis_runtime_crypto` enforces the rejection.
  A source revision alone does not attest an image's selected features.
- Shieldd's `third_party/orbis-crypto` contains upstream BLS12-381 DKG, PRE and
  threshold signing implementations. `upstream.json` identifies their source
  and hashes; this inspection did not execute the provenance check. The
  Shieldd client selects the BLS feature. Its payloads carry opaque Jubjub
  openings; these two curve roles must remain separate in the specification.
- The existing wire API is
  [`orbis.v0.pre.StartPre`](https://github.com/sourcenetwork/orbis-rs/blob/0a0f935a85cc60e87561a9c7364fa80fdb3332df/crates/proto/proto/orbis/v0/pre/pre_service.proto).
  It includes a reader public key and proof of knowledge, object ID, optional
  derivation/salt/window and inline encrypted document. This API namespace
  must not be confused with the ring's negotiated protocol version or
  Shieldd's sealed-package version 2 / audit-selection version 3.
- [PRE ingress](https://github.com/sourcenetwork/orbis-rs/blob/0a0f935a85cc60e87561a9c7364fa80fdb3332df/bin/orbis-node/src/pre/v0/service.rs)
  and [responders](https://github.com/sourcenetwork/orbis-rs/blob/0a0f935a85cc60e87561a9c7364fa80fdb3332df/bin/orbis-node/src/pre/v0/coordinator/handlers.rs)
  check signed JWT claims against reader/object/derivation/salt, independently
  resolve the document and ring, check ACP permission and encryption binding,
  and guard accepted token replays. Responders load the real stored share
  bundle; coordinator verification checks authenticated response statements
  and share proofs. These are real protocol targets, not proof of their
  security or evidence of a live compatible deployment.
  A responder records the token JTI after ACP succeeds but before secret/key
  decoding, share loading, encryption-proof verification and re-encryption.
  Failure at those later stages can therefore consume the token. Model this
  state change and its retry consequences; do not postpone replay insertion
  until a successful release.
  `helpers/jti_replay.rs` implements a per-node in-memory map keyed by JTI;
  restart loses it, and capacity pressure explicitly evicts a still-valid
  token entry. The baseline replay claim is conditional on that entry remaining
  resident, not durable or committee-wide single use.
- [Vera authorization](https://github.com/sourcenetwork/orbis-rs/blob/0a0f935a85cc60e87561a9c7364fa80fdb3332df/crates/authz/src/vera/mod.rs)
  exists. The inspected PRE helper calls its live `check`, not `check_at` with
  a shared height. Its window check bounds the document timestamp; JWT expiry
  is separate. A model must preserve those semantics rather than assume
  globally atomic policy snapshots, current-time disclosure expiry, or
  durable one-time release from a token replay guard.
  Although `check_at` accepts a requested height, `acp_verify_access` performs
  an ABCI query with `prove=false` and returns only the Boolean decision.
  `current_anchor` reads RPC status and `anchor_time` reads an ordinary block
  RPC. The inspected client does not authenticate a policy proof/finalized
  revision or retain the returned query height. Requesting a height or timing
  the call does not establish a verified bounded-freshness claim.
- Shieldd's `crates/disclosure/src/orbis.rs` implements demo sealed delivery
  of accepted Transfer openings, with package, transaction, field/tier,
  policy and epoch checks. The client validates returned ciphertext/context.
  This does not supply a general accepted-capsule release service.
- `crates/core/component/shielded-pool/src/note_seizure.rs` implements the
  request-bound Jubjub capsule DLEQ verifier. It explicitly does not establish
  ACP authorization; its local evidence constructor is test/benchmark gated.
  The inspected upstream protobuf inventory has DKG/PRE/sign/store-secret
  services, but no Shieldd capsule-release, address-DH or PET service. Generic
  Vera ACP existence must not be mislabeled production seizure authorization.

### Minimum correspondence before release qualification

First choose and pin a source-matching BLS runtime image and actual ring
configuration (threshold, members, corruption assumptions, trusted relays,
protocol version, policy source and refresh/reshare behavior). Validate real
wire interoperability with the existing client and genuine threshold nodes.
No startup guard should be removed merely to make that test run.

For generic PRE, a Tamarin model can then map actual ingress, each responder,
ACP decisions, replay state, DKG/share ownership and aggregation to the real
messages above. State cryptographic idealizations separately from library
correctness; include malicious ingress/responders, context substitution,
reader-key substitution, stale policy/token replay and threshold corruption.
Liveness requires explicit online-honest-quorum, communication, stable-policy
and retry assumptions. A design proof under these assumptions is not an
implementation refinement or deployment certificate.

For Shieldd seizure or private audit release, first implement the missing
service contract and enforce accepted-note provenance plus the authority's
exact capsule grant before any opening/share is returned. Bind chain, capsule,
note, asset, key epoch, policy, authority instruction and expiry, and specify
revocation/retry behavior. Implement the required Jubjub threshold operation
and ownership/PET path if that feature is intended, then exercise unauthorized,
wrong-owner/capsule, stale-epoch and replay cases against those real handlers.
Only those existing handlers may become the production Tamarin target; a
model containing assumed `AuthorizedRelease` rules cannot close this gate.

## Enabled settlement consumers and remaining qualification

The inspected Bankd d85 source has two deposit paths and two withdrawal
destinations. `keeper/msg_server.go` sends an SDK deposit directly to Shieldd;
the SHLD precompile queues an escrowed deposit for `pending.go` EndBlock minting.
`withdrawals.go` matches the number, order and destination of execution-client
withdrawals against the canonical transaction. Direct transfers release escrow;
`host_execution.go` runs ordered EVM calls in a cached context and re-mints a
proof-bound refund note if conversion, execution or residual-asset checks fail.
`turnstile.go` excludes pending deposits from available escrow per denomination.

Existing tests are useful qualification inputs, not results for the new pin:

| Consumer | Existing concrete tests | Remaining joint obligation |
| --- | --- | --- |
| SDK deposit and spend | `TestDepositAndSpendTxAgainstShielddExecution` | New candidate rerun; exact note/effect identity and persistent interrupted commit |
| Queued precompile deposit | `TestSHLDPrecompileDepositAgainstShielddSidecar`, `TestSHLDPrecompileDepositRollback` | First name predates embedded backend; rollback test discards CacheContext, so add a genuinely reverting EVM call and durable drain/replay case |
| Direct host withdrawal | `TestDepositAndHostWithdrawalAgainstShielddExecution` | Exact typed replay rejection, persisted escrow/nullifier/output equality, genuine response-mismatch and commit-failure controls |
| EVM success | `TestHostExecutionWithdrawalDepositsForBeneficiary` | Persistent joint recovery and multi-action ordering/fee interactions |
| EVM refund | `TestHostExecutionWithdrawalRefundsAfterRevert`, `TestHostExecutionWithdrawalRefundsResidualAsset` | Exact once-only refund after real restart; native forwarding faults between acceptance, settlement and joint commit |
| Escrow defense | `TestIntegrationTurnstileRejectsAndMovesNoCoins`, `TestIntegrationEscrowConservation`, `TestIntegrationMultipleWithdrawalsSameBlock` | These use a real Cosmos bank but fake Shieldd; retain that scope and supplement genuine native effects |

The first five rows live in `shieldd_integration`; escrow tests live in
`x/shieldd/keeper/turnstile_integration_test.go`. Genuine private-fee and
multi-action transactions remain required; the newly authored Transfer
conflict/recovery tests alone do not close those cases. Native forwarding
controls must alter only delivery/failure scheduling or the returned response,
never fabricate successful proof verification or replacement state roots.

The next authored tests are still **uncompiled and unexecuted**:

- `TestGenuineWithdrawalPersistentSettlementAndResponseMismatch` forwards real
  native withdrawal effects, omits one successful response, requires actual
  rollback, then verifies retry and payout after both stores reopen.
- `TestGenuineMultiActionPrivateFeeAtomicityAndCustody` funds two `ubrl` notes
  and a separate `ushieldd` fee note through real SDK deposits. It checks three
  genuine proofs, distinct action keys/nullifiers, exact compact ordering,
  durable effects and `E=L+P+F` with `P=0,F=1`. Its wrong-fee-proof and second
  action-signature controls establish stateless admission/no-effects; they do
  not exercise failure after an earlier action has executed.
- `TestGenuineHostRefundPersistentSettlementAndMintFailure` executes the real
  EVM approve/revert/refund path. An injected error follows a successful native
  refund mint, requiring actual rollback and unchanged durable identities.
  A reopened retry must refund once, and a genuine spend of that refund must
  produce the exact persistent payout and escrow result.
- `TestSHLDPrecompileActualFrameRevertAndDrain` executes a genuine nested EVM
  CALL to SHLD before an outer REVERT, with distinct inner-failure and
  outer-revert markers. It observes queue contents, sequence and custody,
  and every actual native Deposit attempt during the positive and rejected
  drains. Its empty drain retry reaches the genuine already-ended phase
  rejection without minting again. This uses the existing ApplyMessage/keeper
  lifecycle; signed-EVM ante, FinalizeBlock and persistent joint commit remain
  separate obligations.

- `TestSHLDSignedEVMDeferredDepositPersistent` sends a genuinely signed Ethereum
  transaction through recovered-sender ante, FinalizeBlock and Commit. It
  distinguishes an executed outer revert from ante failure; checks gas/nonce in
  `aatom` separately from `ubrl` custody; and reopens both stores before checking
  compact mint payloads, the source-position host receipt and decrypted wallet
  balance. A real subsequent empty block must make no native mint attempt.
  The compact transaction ID is intentionally stripped; the persisted receipt
  supplies the retained source binding. This source is not yet compiled or run.
These are orderly reopen and deterministic call-boundary controls, not process
kill, power-loss or network-consensus evidence. They require newly corresponding
builders/native artifacts; earlier candidate receipts do not cover the edits.

The approved consumer source checkpoint binds the seven Bankd test files and
the spend builder's manifest/source. Their exact bytes were rechecked on
2026-09-29; this is source identity, not compilation or execution. Capture a new
immutable consumer candidate before running them, preserving the earlier
Transfer/recovery snapshots and artifact receipts. The consumer builder and the
same-worker allocation diagnostic have different `main.rs` sources. A successful
resource comparison cannot qualify the consumer builder; any combined source
requires its own review, source identity and build. Keep the full protobuf,
native archive, builder, registry and CGO link identities together. Do not reuse
the old single-Transfer fixture for a new action/fee shape or construct a
synthetic verified capability to replace genuine proof admission.

No production Bankd `SeizeNote` caller was found in this source: generated
protobuf messages are not a settlement route. `ApplyComplianceAction` has an
embedded client wrapper and test, but no Bankd policy-admission caller. Runtime
proof-family qualification and actual enabled Bankd consumer qualification are
therefore separate gates. Adding a seizure/authority route would require its
real authorization, accounting and recovery design; this inventory does not
invent one to make the family table appear complete.

Private fees use Shieldd's `ushieldd` base asset; the current Bankd integration
fixture's `ubrl` deposits cannot fund them. A nonzero-fee test must fund a real
base-asset note separately. The current runtime `FeePay` records paid-fee events
and block-local base/tip totals; `FeeComponent.end_block` emits `EventBlockFees`.
No Bankd fee-event payout/burn consumer was found in the inspected source or a
corresponding policy in the current wallet/protocol documentation. The present
host escrow therefore retains those coins while shielded output value decreases.
Qualification must observe that custody surplus and its replay/recovery behavior;
it must not assert an invented host payout, burn or beneficiary. The selected
qualification contract observes `E=L+P+F` per denomination without adding
duplicated reserve state. The existing withdrawal bound `W<=E-P` includes fee
surplus `F`; it does not establish `W<=L` independently of valid proof soundness.
