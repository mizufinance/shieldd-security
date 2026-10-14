# Native inverse window proofs on Mac

Four modules and 22 declaration/type/axiom audits passed under the existing Mac native guard: one thread, 1536 MiB Lean heap, 4 GiB process-group RSS, and 240 seconds per module. The pinned runtime is `844389ee069e1fb2e576708842d0b389b4d9a44a`.

The package checks natural-number quotient arithmetic, bounded shift/mask semantics, aligned word values, and joint CLZ bounds with the zero-window fallback.

The source derives from desktop transport `bc09493941663fdda4597d3e40a45a2bc7a43495`. Original drafts are retained under `desktop-source`; Mac variants remove unnecessary imports, rename the reserved `prefix` binder, normalize conditional branches, and expose a structure projection to the arithmetic tactic. Theorem statements are unchanged apart from the binder rename.

Selected-limb correspondence, complete-input correspondence in nonfallback cases, inverse progress and the full inverse core, compiled native execution, and full Transfer endpoints remain OPEN. Native credit is 0; certification is false. No circuit assertion positions are added.

Source and atomic qualified evidence are committed separately. Failed replays receive no credit.
