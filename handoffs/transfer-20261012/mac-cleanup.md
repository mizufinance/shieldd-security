# Mac disk cleanup suggestions

The Mac had approximately 3.5 GiB available during the 12 October 2026 inventory. The most useful first cleanup is the 23 GiB Go build cache. Removing disposable download and build caches can restore proof-build headroom without touching the Transfer campaign's original sources or evidence. Nothing was deleted during this inventory.

Sizes below are approximate allocated disk usage from `du`, except individual installer sizes, which are file lengths. Actual reclaimed space may differ because of APFS snapshots and shared blocks.

## First candidates

| Priority | Exact path | Approximate size | Consequence |
| --- | --- | --- | --- |
| 1 | `/Users/antoinecyr/Library/Caches/go-build` | 23 GiB | Rebuildable Go compiler cache. Prefer `go clean -cache` when the installed Go tool owns this path; future Go builds take longer |
| 2 | `/Users/antoinecyr/.npm/_cacache` | 2.3 GiB | npm package download cache; future installs download packages again |
| 3 | `/Users/antoinecyr/Library/Caches/com.microsoft.VSCode.ShipIt/update.VoEMWcq` | 1.4 GiB | Staged VS Code update; remove only after confirming no updater is using it. An update may download again |
| 4 | `/Users/antoinecyr/.npm/_npx` | 469 MiB | Rebuildable npx tool installations; commands may reinstall them |
| 5 | `/Users/antoinecyr/Documents/Source/shieldd-web/.turbo` | 172 MiB | Rebuildable web task cache; subsequent builds rerun cached tasks |

The first two directories alone contain about 25 GiB. This should provide considerably more useful headroom than deleting proof files. No active Go, Cargo or Lean compiler appeared in the process census, but recheck before actually clearing build caches.

## Downloaded installers

These are additional candidates if the applications are already installed and the installer copies are no longer needed. They are not application data.

| Exact file | Approximate size |
| --- | --- |
| `/Users/antoinecyr/Downloads/ChatGPT.dmg` | 615 MiB |
| `/Users/antoinecyr/Downloads/Codex (1).dmg` | 293 MiB |
| `/Users/antoinecyr/Downloads/Claude.dmg` | 217 MiB |
| `/Users/antoinecyr/Downloads/Antigravity.dmg` | 184 MiB |
| `/Users/antoinecyr/Downloads/Codex.dmg` | 150 MiB |
| `/Users/antoinecyr/Downloads/gents-desktop_0.19.0_aarch64.dmg` | 98 MiB |
| `/Users/antoinecyr/Downloads/gents-desktop_0.18.5_aarch64.dmg` | 88 MiB |

These seven installer files total approximately 1.61 GiB. Eject any mounted installer before removing its disk image.

## Larger optional cleanup

| Exact path | Approximate size | Qualification before removal |
| --- | --- | --- |
| `/Users/antoinecyr/Documents/Source/shieldd/target/ci/deps` | 28 GiB | Cargo CI dependency outputs. Confirm no separate session or retained evidence needs these specific binaries; future CI-profile builds recompile |
| `/Users/antoinecyr/Documents/Source/shieldd/target/ci` | 30 GiB | Includes the preceding 28 GiB, so do not add the sizes. It contains compiled CI outputs and examples; confirm consumers first |
| `/Users/antoinecyr/Documents/Source/shieldd-web/node_modules` | 3.1 GiB | Dependency installation; preserve manifests/lockfiles and reinstall before web work |
| `/Users/antoinecyr/Documents/Source/bankd/node_modules` | 1.8 GiB | Dependency installation; preserve manifests/lockfiles and reinstall before bankd work |

The whole Shieldd `target` directory occupies 55 GiB, but it also contains specialized artifacts. Prefer the identified CI cache after its consumers are checked instead of indiscriminately deleting the entire directory. Do not count both `target` and its children as separate savings.

## Preserve

- The Transfer campaign root `/Users/antoinecyr/Documents/Codex/2026-10-08/can`, including original captures, SQLite database, sources, receipts, rejected attempts, source selections and lossless archives. Its 16 GiB is evidence and working material, not a disposable cache.
- `.git`, `shieldd.lock`, generated Lean sources, input data, proof manifests, toolchains and exact package sources needed by the selected replay.
- Codex session/history and recovery files under `/Users/antoinecyr/.codex/sessions` and `/Users/antoinecyr/.codex/archived_sessions`.
- The 6.6 GiB under `/Users/antoinecyr/Documents/Source/shieldd/tmp`: the largest subdirectories contain `network_data`, which may be persistent local node state rather than temporary compilation output.
- The 20 GiB Shieldd `.git` directory. Safe Git packing would require its own headroom and repository audit; manual object deletion is inappropriate.
- The 15 GiB Rust toolchain directory until each toolchain's active project and proof dependencies are checked.

No deletion approval or deletion action is implied by this suggestion list.
