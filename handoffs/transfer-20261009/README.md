# Transfer proof coordination

Both machines share `codex/security-assurance` in `mizufinance/shieldd-security`.
Runtime pin: `844389ee069e1fb2e576708842d0b389b4d9a44a`.
Full Transfer assurance remains OPEN.

The desktop chat **Transfer proof** owns Windows proof/native builds. The new
local GPT-6.1 Sol/high subagent owns the Mac build lane. This parent chat
orchestrates integration and evidence acceptance; local Claude Opus 5.5 performs
independent review. The stopped predecessor chats remain historical context.
One bounded heavy verification job may run on each physical machine, as
explicitly authorized by the user. See [the completion plan](completion-plan.md).

The publication lock now matches the clean runtime snapshot at the full SHA
above. The reduced baseline, nine compiler dependencies and bounded capture data
tools are integrated; the remaining semantic/native sources are still under
scoped review. No historical receipt is recertified by this pin reconciliation.

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

## Worker arrangement — implementation authorized 2026-10-09

The user instructed the new parent chat to implement the completion plan using
local Sol 6.1/high, the desktop **Transfer proof** chat, and local Opus 5.5.
This supersedes the earlier parent-only Mac arrangement. The former M15 worker
remains retired; the new worker is a separate agent. Parent serializes pushes
and verifies received source identities. No recurring coordination automation.
