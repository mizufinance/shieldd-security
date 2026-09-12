# Native Decaf assurance

This pilot checks the Rust and Go libraries independently of Shieldd's circuit
evidence. `inputs.json` pins the original and candidate revisions. The candidate
libraries are not necessarily selected by a Shieldd or Orbis deployment.

## Run

```sh
python3 -m unittest discover -s tests -p test_decaf.py
python3 decaf.py functional
python3 decaf.py leakage
```

For native Linux x86-64 tools (also used by the CI workflow):

```sh
docker build --platform linux/amd64 -f decaf/Dockerfile -t decaf-fv .
docker run --rm --platform linux/amd64 --cpus 2 --memory 4g --memory-swap 4g \
  --cap-add SYS_PTRACE --security-opt seccomp=unconfined \
  -v "$PWD:/workspace" decaf-fv python3 decaf.py leakage
```

Run jobs serially. The runner shares the repository's exclusive verification
lock. The feasibility pilot gives each analysis five minutes; build/test steps
have a 30-minute limit. Reports and logs are in
`.work/decaf/{functional,leakage}-report/`; build inputs are disposable copies.
The container needs debugger permissions to snapshot its own harness process.
On ARM64 hosts, use the native Linux CI job: emulation may run BINSEC but cannot
necessarily supply GDB's initialized core snapshot.

## Leakage property and boundary

For the same initialized public process state, memory layout, public lengths,
and public generator, changing valid secret inputs must preserve branch and
memory-address traces and termination through the designated output boundary.
The core dump initializes the runtime and heap before secrets become symbolic;
the runner does not replace arithmetic, allocation, or runtime calls with stubs.

The Rust pilot makes the 32-byte `Fr` Montgomery representation symbolic and
restricts it to values below the scalar modulus. This covers every scalar for
the pinned default backend, but not scalar construction or a secret input point.
Both ordinary multiplication and mutable-reference assignment are entry points.
The output is retained as an `Element`; compression is a separate obligation.

The Go pilot makes all 256 input bits symbolic and calls uniform scalar reduction
followed by native multiplication of the public generator. The snapshot includes
initialized moduli and the public base. The output remains a point. Encoding,
canonical parsing, secret input points, scheduling, and arbitrary allocator
states require additional analysis. One public snapshot is not a proof for every
deployment, public base, or runtime state.

The Go snapshot uses `GOMAXPROCS=1`, `GOGC=off`, and
`GODEBUG=memprofilerate=0` to avoid unrelated concurrent collection and sampling
in the pilot. These are recorded public runtime settings, not substituted code.
Production collector/profiler configurations remain uncovered.

Instruction latency, speculative execution, power/EM, faults, and secret erasure
are outside this branch/address model. Output disclosure is permitted only at
the named final boundary; it does not excuse leaks during computation.

## Evidence interpretation

Functional tests and relational analysis are different evidence kinds. Checks
have `passed`, `failed`, or `blocked` outcomes; every report has
`full_certification: false`. Aggregate success also requires `completed: true`;
interrupted or partially executed runs cannot pass. BINSEC's `secure` verdict is accepted only with a
reached output boundary and no incomplete-analysis diagnostic. Its `unknown`,
unsupported operations, missing tools, and exhausted bounds cannot establish a
proof. Helper results never promote unexamined caller paths.

Original revisions and a controlled mutable-assignment routing mutation are
negative cases. Independent C controls exercise branch leakage, address leakage,
and a safe operation. A negative case passes only on an actual leakage diagnostic;
a build error is not detection. The dependency-omission control attempts to
replace reached arithmetic with an assumed-safe return; configuration validation
rejects such summaries and path cuts. A separate manifest test rejects incomplete
revision identities. No library revision is silently assumed safe.

Reports bind source trees, dependency locks, harnesses, binaries, snapshots, build
commands and analysis configuration. CI regenerates results rather than reusing
proof verdicts. Snapshot and binary hashes describe the artifact actually checked,
not another compiler build of the same source. Each analyzed case retains a
compressed binary/core/configuration reproducer, including hashed file-backed
mappings. After unpacking, replay with
`binsec -sse -checkct -checkct-leak-info halt -sse-script analysis.cfg -sse-sysroot mapped-files -sse-depth 100000000 -sse-timeout 300 core`.

See [coverage](coverage.md) for consumer joins and remaining obligations.
BINSEC's [relational analysis](https://github.com/binsec/binsec/blob/dfe4739f03a474cf2ebc5ae419760e57ce0050c3/doc/sse/relse.md)
and [initialized core analysis](https://github.com/binsec/binsec/blob/dfe4739f03a474cf2ebc5ae419760e57ce0050c3/doc/sse/intermediates_2.md)
define the underlying tool model.
