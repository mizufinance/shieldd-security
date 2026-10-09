# Shieldd security

This repository owns one security CLI, claim register and Lean package for the exact
runtime revision in `shieldd.lock`: `844389ee069e1fb2e576708842d0b389b4d9a44a`.
Runtime changes belong in Shieldd. This draft delivers a reduced PR160 Transfer
slice and retires the earlier Decaf, gnark and SnarkPack stacks; it does not certify
Transfer or the complete system.

The reduced work comprises the executed direct-Lean/Clean four-gate comparison,
the direct-Lean architecture decision, and ordered 64-field projection plus five
canonical permanent-spend field-gate theorems. See the
[results, decision and evidence boundaries](docs/pr160-transfer-slice.md).

Run the light checks with Python 3.13:

```sh
python -m pip install -r circuits/requirements.txt
python -m unittest discover -s tests
python security.py check
```

The [Transfer completion campaign](handoffs/transfer-20261009/completion-plan.md)
adds reusable compiler soundness/completeness interfaces and bounded source-graph,
binary-row and certificate readers under `circuits/`. The readers check data
framing and exact row comparison; they do not prove Transfer semantics. Their
small fixtures run in ordinary CI. Full captures, build logs and compiler caches
remain local, with scoped identities and outcomes retained in the handoff packets.
The concrete full-graph instance, legal-assertion derivation and native/state
consequence remain open.

The existing narrow integration entry point is:

```sh
python security.py circuits --scope transfer-slice
```

It requires a clean pinned runtime checkout and independently qualified local
receipts/raw captures. Those ignored `.work` artifacts are **not delivered by this
PR**. An unprepared checkout fails closed. The register therefore carries no
published receipt SHA for this new source tree. The historical local receipt is
not certification of this branch or a portable CI result.

PR CI runs light policy and unit tests. Heavy pilot jobs are manual only, require
the pinned Linux toolchains and explicit resource supervision, and remain broader
than the reduced delivery. See [verification boundaries](docs/verification.md)
and [state prerequisites](state/README.md). `python security.py release` remains
blocked. Full-family proofs, runtime row correspondence, cryptographic/verification
key correspondence and state replay/durability claims remain open.
