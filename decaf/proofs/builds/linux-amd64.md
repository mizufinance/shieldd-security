# Linux AMD64 proof-tool builds

This records native tool provenance, not completed native proofs or a
constant-time certification. Builds ran in Ubuntu WSL2 on the desktop.
Goose, Fiat and hax have independently reviewed native Linux identities.

## hax

- Source: `d8b5b3d3b666fee8943a351445d2b680105e8ea3`, version 0.3.7,
  with a clean working tree and no source patch.
- Rust: `nightly-2025-11-08`, compiler commit
  `843f8ce2ebc01d35a30484eadc8a84cdc6130844`, Linux x86-64.
- OCaml build dependencies: OCaml 5.1.1, Dune 3.24.0, Base v0.17.3,
  Core v0.17.2, Yojson 3.0.0 and ppxlib 0.35.0. These belong to the engine
  build environment; the Rocq proof environment uses OCaml 5.3.0.

Rust components `cli/driver`, `cli/subcommands`, `engine/names/extract` and
`rust-engine` were installed with `cargo +nightly-2025-11-08 install --locked
--debug --jobs 2 --root /root/.opam/hax-0.3.7 --path COMPONENT`. The source and
Cargo target caches were on WSL's native filesystem.

The engine reused installed OCaml dependencies from the existing `hax` switch
read-only. It built with `OCAMLRUNPARAM=o=20 opam exec --switch=hax -- dune build
-j 1`, then `dune install --profile dev --prefix /root/.opam/hax-0.3.7` under the
same switch. Explicit paths selected the newly built names/schema exporters.
The separate `hax-0.3.7` switch was created empty; the existing hax installation
was not replaced. The serial engine build reused completed objects and stayed
under the same 4 GiB cap that had stopped the initial build.

| Executable | SHA-256 |
| --- | --- |
| cargo-hax | `51cee5c850edb342037ec950b4dfa44be555a78d30d50f22195e48a2f3697f35` |
| driver-hax-frontend-exporter | `a5f45f5c0afe6b51942882a9bcf5f8b65c42b9c8a563e97fb6405bfb50271858` |
| hax-engine | `2da24f073f5888e8151313061bb067626f36c69ec4288efeb721661607749eb8` |

An independent read-only review verified the live hashes, clean pinned source,
Linux ELF identities, isolated executable resolution, CLI version/commit,
compiler identity and build log. It did not perform a separate rebuild or
establish extraction correctness.

## Fiat

- Source: Fiat-Crypto `e0a0a97d201ec1709d9ac11f1dce47c19468bf9e`,
  with recursive submodules at their recorded commits.
- Applied patch: `fiat-array-index.patch`, SHA-256
  `4fff2e3baaea03ea181cad9d825928493be5d67f6b08058879925c0e9faf0870`.
- Build tools: OCaml 5.3.0, Rocq runtime 9.2.0, Rocq standard library
  9.1.0, `coq-core` compatibility commands 9.2.0, ocamlfind 1.9.8,
  Zarith 1.14 and Dune 3.23.1.
- Build command:

```sh
opam exec --switch=decaf-fv -- \
  make -C .cache/fiat-crypto -j1 SKIP_BEDROCK2=1 standalone-unified-ocaml
sha256sum .cache/fiat-crypto/src/ExtractionOCaml/fiat_crypto
```

The resulting Linux x86-64 ELF executable SHA-256 is
`f197dbebfefb1ff983aee468201b55c0395450fb97e7d08e33c7eb2cba6f94ef`.
The successful serial build reused completed objects from the same source and
toolchain. The preceding two-worker build exceeded its 4 GiB job limit; the
serial build completed under that same limit. The source cache was on WSL's
native filesystem, linked from `.cache/fiat-crypto`. An independent read-only
review verified the live revision, exact source diff, all ten recursive
submodule revisions and clean working trees, executable hash and ELF identity
before registration. It inspected the successful build log and tool versions;
it did not perform a second independent rebuild.

The source-diff comparison and recursive submodule checks are also enforced by
`decaf_generate.py`. A build identity establishes provenance, not the printer's
semantic correspondence, native field correctness or compiled leakage bounds.

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
