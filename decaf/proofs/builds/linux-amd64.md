# Linux AMD64 proof-tool builds

This records native tool provenance, not completed native proofs or a
constant-time certification. Builds ran in Ubuntu WSL2 on the desktop.
Only Goose is registered so far; Linux Fiat and hax identities remain absent
and their runners reject this host until their builds are reviewed.

## Goose

- Source: Perennial `3fe5d0a957a95c27cff204e729a5e96a3e3217ad`.
- Applied patch: `perennial-native.patch`, SHA-256
  `384a116c642d0046a38519b0e338ea07d684ddf29f5d0de1162e202f2fb1a56f`.
- Build tool: Go `go1.26.4`, `GOOS=linux`, `GOARCH=amd64`, `GOAMD64=v1`.
- Build command, from `.cache/perennial`:

```sh
GOTOOLCHAIN=go1.26.4 GOMAXPROCS=2 GOFLAGS= GOWORK=off \
  go build -p 2 -trimpath -o ../goose ./goose/cmd/goose
go version -m ../goose
sha256sum ../goose
```

The resulting executable SHA-256 is
`69af08e70ae0dd65fb2a424e4106ce63b7e9c3edb8105b97e33567bd420a2bfe`.
Embedded build metadata records the exact revision and `vcs.modified=true`
for the reviewed patch. An independent read-only review checked the executable
hash, embedded metadata, pinned revision, exact patch diff, and dependency
versions/checksums against `go.mod`/`go.sum` before registration.

The source-diff comparison is:

```sh
git -C .cache/perennial diff --binary --abbrev=7 HEAD
```

Its text must equal the committed patch. The runner continues to enforce both
source-patch and executable identities at replay time. Go compiler correctness,
Goose translation correctness, and host environment behavior remain explicit
trusted boundaries; these provenance checks do not prove them.

## Rocq support environment

The desktop switch `decaf-fv` uses OCaml 5.3.0, Rocq runtime 9.2.0,
Rocq standard library 9.1.0 and `coq-core` compatibility commands 9.2.0.
The older `coq` umbrella-package dependency in some pinned support packages
selects an incompatible downgrade. Install Iris with the exact runtime/library
versions specified, and build the remaining pinned support sources with the
installed compatibility commands. Do not accept a solver-selected downgrade
as equivalent to the pinned toolchain.
