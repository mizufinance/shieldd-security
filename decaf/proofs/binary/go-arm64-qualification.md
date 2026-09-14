# Go64 ARM64 multiplication qualification

Run `python3 decaf_go_arm64_qualify.py --goroot <Go-1.25.4-root>
--dune-root <qualified-BINSEC-source>` after refreshing the eight-case candidate
architecture qualification with `decaf_qualify.py --rust-fq-add --dune-root ...`.

This check compiles the adopted Go64 Fq and Fr multiplication sources unchanged
into an ARM64 Linux harness. Both operations execute before the declared output
boundary. The 64-byte input buffer is independently secret, without constraints
relating secrets to a public key. Arbitrary input words strengthen this trace
property; they do not change the arithmetic API's reduced-input contract.

The entry state fixes SP, the goroutine pointer, stack bounds, and stack guard.
This exercises the actual compiled stack checks, loads, stores, carry chains,
and high multiplication instruction. It does not cover every permitted runtime
state, preemption, GC, scheduling, consumer binary, or hardware leakage channel.
Runtime settings are recorded, but a standalone initialized entry-state analysis
does not establish a claim about all executions with those settings.

Two separate source controls insert a secret branch and a secret-dependent
table address. Acceptance requires each intended leak, a reached output boundary,
and complete exploration statistics. Errors, omitted instructions, timeouts,
missing boundaries, pending paths, discontinued paths, and failed assertions are
rejected. Source trees are fresh per run to exclude stale build inputs.

The runner binds its helpers, matrix, generation recipe, source files, harness,
compiler and runtime sources, binary, analysis configuration, candidate analyzer
components, solver selection, and command logs. It rechecks identities before
acceptance and writes the report atomically. Installed component inventory is
not an attestation of actual dynamic loading; that qualification remains open.

The report under `.work/decaf-go-arm64-qualification` always retains
`qualification_complete: false` and `full_certification: false`. Cross-compiling
and symbolic analysis do not provide native ARM64 benchmark measurements.
