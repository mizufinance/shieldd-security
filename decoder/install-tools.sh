#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools="$root/.cache/decoder-tools"
mkdir -p "$tools"
export CARGO_BUILD_JOBS=2 OPAMJOBS=2 RAYON_NUM_THREADS=2
apt-get update
apt-get install -y --no-install-recommends python3-venv
python3 -m venv "$tools/python"
"$tools/python/bin/pip" install z3-solver==4.14.1.0
if [ ! -d "$tools/hax/.git" ]; then
    git clone --filter=blob:none https://github.com/cryspen/hax.git "$tools/hax"
fi
git -C "$tools/hax" checkout --detach d8b5b3d3b666fee8943a351445d2b680105e8ea3
test "$(git -C "$tools/hax" rev-parse HEAD)" = d8b5b3d3b666fee8943a351445d2b680105e8ea3
eval "$(opam env --switch=hax --set-switch)"
(cd "$tools/hax" && ./setup.sh -j 2 --no-cleanup)
curl --fail --location --retry 3 \
    https://github.com/FStarLang/FStar/releases/download/v2026.05.24/fstar-v2026.05.24-Linux-x86_64.tar.gz \
    --output "$tools/fstar.tar.gz"
echo "2a993133f71e1a020b69fb706092663a66748016bd69c44950eb9cde9d8edbe8  $tools/fstar.tar.gz" | sha256sum --check
mkdir -p "$tools/fstar"
tar -xzf "$tools/fstar.tar.gz" -C "$tools/fstar" --strip-components=1
echo "$tools/python/bin" >> "$GITHUB_PATH"
echo "$tools/fstar/bin" >> "$GITHUB_PATH"
echo "HAX_PROOF_LIBS_HOME=$tools/hax/hax-lib/proof-libs/fstar" >> "$GITHUB_ENV"
