# Transfer plan review record

On 2026-10-02 Claude Code 2.1.280 reviewed a frozen copy of the initial
[Transfer plan](transfer-proof-plan.md), the existing verification boundaries,
AGENTS.md, historical Transfer semantics/refinement, and current pinned runtime
Transfer constructor/proof wrapper. It used read-only tools and made no edits.

The actual response reports only `claude-opus-5-5` in `modelUsage`, with
`canonicalModel: claude-opus-5-5`, `is_error: false`, `subtype: success` and nine
turns. The supervising process exited zero in 208.04 seconds; frozen input bytes
were unchanged. This establishes the requested model review, not theorem validity.

Verdict: **APPROVE WITH REQUIRED CHANGES**. T0 may begin; the substantive changes
must be reflected before the affected later stages are accepted. The plan's
numbered review-refinements section records all fifteen findings and their
implementation requirements: setup provenance; relation-digest/existential
soundness anchor; multi-instance upstream contracts; registry invariants; two
scalar moduli; mixed-family conservation limits; commitment consumers; volume
history; intent discrepancies; dummy effects; scalable templates; privacy leakage;
transcript binding; dependency-aware stage gates; and Rust completeness tests.

The upstream-security boundary is preserved. Review observations about gadget
internals or upstream security were not verified by this review and remain tasks
to check at their precise application boundary. In particular the revision uses
a computational collision bound rather than absolute dummy/real hash-range
disjointness; makes simulation-extractability conditional on the security game;
and requires inspecting actual setup secret-handling requirements rather than
asserting a setup design from the review alone. Subsequent parent inspection of
pinned `docs/compliance/flow.md`, `docs/nullifier-history.md` and `volume.rs`
corrected the proposed trace property to undisclosed volume, not all outbound
volume, and distinguished permanent spend nullifiers from day-scoped volume
nullifiers. These source observations are not executed proofs.

Later source checks also distinguished current circuit-enforced EPK/ownership
nonidentity from honest entropy assumptions, and current paired compliance
snapshots with grace/freeze rules from historical current-root-only admission.
The routing intent now cites the pinned `docs/routing.md`. These refinements are
source-grounded implementation review, not an additional Opus review or proof.

Retained local raw records (ignored, not generated proof evidence):

- `.work/diagnostics/transfer-plan-review-20261002/inputs/PLAN.md`: reviewed version.
- `inputs.json`: frozen review input digests.
- `stdout.json`: actual provider response and model usage.
- `review.md`: extracted complete review text.
- `run.json`: process outcome, memory observation and unchanged-input check.

The final revised plan incorporates these requirements but has not had a second
Opus review. GPT-6.1 Sol must preserve the conditional verdict and keep incomplete
proof/application joins open; this review does not promote any assurance gate.

After review the user explicitly selected pre-deployment assurance with setup
assumptions. Correct key generation is therefore a named premise; proving the
actual loading, relation matching and API use remains Shieldd's obligation.
Missing deployment registry artifacts are a later deployment gate, not a blocker
for this conditional integration proof. The revised plan records this scope.
Parent source inspection also recorded that this pin's loader requires the
`development` setup label and a complete v2 registry. That accepted label is
not evidence of setup-secret handling or deployment qualification.
The plan also distinguishes circuit-legal zero balance blinding from the
native nonidentity aggregate binding-key requirement for proof-bearing
transactions; circuit completeness does not alone establish transaction
constructibility. This is a source-review refinement, not another Opus review.

Implementation source review compared the independent Transfer semantic draft
with the pinned constructor and its registry, compliance, authorization, note,
recovery, volume, routing and encryption components. It corrected tree framing
to a fixed tree domain with five inputs (level plus one, then four children),
scalar-reduction bounds and canonical field subtraction. The public projection
uses Transfer's exact 64-field order, which differs from the encryption payload's
standalone projection; routing fields name permuted slots rather than fixed
recipient/change roles. This comparison and successful Lean elaboration do not
prove correspondence with arbitrary satisfying circuit assignments. Full source,
row, native-operation and application joins remain required.

The ownership/volume composition also needs to distinguish collisions after
IVK scalar reduction from collisions in the full-field hash. Different hash
outputs separated by a multiple of the subgroup order yield the same IVK.
The revised plan requires an explicit construction bound or an unresolved
reduced-key binding assumption before claiming unique volume origins for an
owner. This is a proof-boundary observation, not evidence of a practical attack
or an additional Opus review.

Exact modulus arithmetic further gives `p = 8*r +
43182373549099571680785400801115150921`, so reduction has at most nine
canonical field preimages per scalar. The plan records the corresponding
conditional random-oracle union bound as a construction argument to formalize.
It does not infer that model from ordinary Poseidon collision resistance or
claim its ownership/key-game composition is already proved.

Narrow Lean checks now also use the already installed native Windows toolchain
at the same recorded version after guarded WSL checks encountered host memory
pressure. The one-heavy-job, finite-budget and memory-stop requirements remain
in force. This execution adjustment is not an additional plan review.
