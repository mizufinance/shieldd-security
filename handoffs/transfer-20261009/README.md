# Transfer proof coordination

Both machines share `codex/security-assurance` in `mizufinance/shieldd-security`.
Runtime pin: `844389ee069e1fb2e576708842d0b389b4d9a44a`.
Full Transfer assurance remains OPEN.

The Windows chat, **Resume Transfer assurance proofs**, owns the full proof
composition and integration, the native/field/DH chain, and the inverse checks
3131–3136. The Mac agent owns independent finite native/compiled-row checks,
the completed fixed empty-input hash build, and explicitly assigned independent
proof obligations. The coordinator owns independent review and the task queue.
One bounded heavy verification job may run on each physical machine, as
explicitly authorized by the user.

## Synchronization

1. The desktop publishes first. The Mac fetches that exact commit and publishes
   its scoped sources and portable receipts on top.
2. Announce the publishing owner to the other worker/coordinator. Before pushing, fetch the shared
   branch and rebase only unpublished commits. Never force push. If a competing
   fast-forward push wins, fetch/rebase and recheck the scoped staged sources before
   retrying. Workers may publish their owned packets without waiting for a new
   interactive coordinator turn; independent review remains pending until performed.
3. After every push, the other machine fetches and acknowledges the exact origin
   commit. A local build may retain frozen earlier source inputs; its receipt must
   identify those bytes rather than silently attributing the run to the latest tip.
4. Use a separate clean publication checkout when an active build depends on the
   primary working tree. Do not reset or overwrite ongoing local proof work.
5. Publish bounded proof sources, recipes, input identities, scoped receipts and
   machine status. Retain logs, compiled objects, toolchains, caches, credentials,
   archives and composed runtime workspaces locally.

Each machine owns its own `sources/mac`, `sources/windows`, `receipts/mac`,
`receipts/windows`, and `status/<machine>.json`. The coordinator owns this README
and `status/coordinator.json`. Receipts use immutable task IDs and source hashes;
do not rewrite completed receipts. Status records are dated observations, not a
claim that a process is still running indefinitely.

## Evidence

`sources/mac` contains reviewable source artifacts rather than a production
runtime patch. M2–M9 are scoped Lean/model/native component results; their exact
premises are retained. `native-fixed05` contains the final successful fixed hash
candidate, including parameter-only dependency projections. Its source contract
records the original UNRUN handoff and is retained as provenance; the successful
build receipt and independent parent review qualify candidate05 alone. Earlier
failed candidates earn no verification credit.

M11 and M12 are finite native and actual compiled-row tests. Their diagnostic
adapters are for disposable replay, and independent removal restores the pinned
PARI source. No setup, prover or verifier was invoked. Parent review checks source
identity and the recorded execution census; it does not claim an independent
native rerun. The all-zero row-vector scope control is outside canonical witness
construction and does not establish an accepted transaction or vulnerability.

Original seal manifests identify locally retained files, including omitted logs.
`receipts/mac/publication-manifest.json` lists the files actually shipped here.
This directory does not refresh the claim register or certify full Transfer.

## Worker arrangement — user update 2026-10-09

The existing Mac subagent will finish and seal its current M15 committed-blinding
range bridge, then stop. Do not reuse or assign further work to that agent.
The parent coordinator takes over all subsequent Mac proof/build work and
coordinates directly with the Windows chat. Existing completed sources and
receipts remain available for independent review and integration.
