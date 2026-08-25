#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GNARK="$ROOT/tools/gnark"
selection="${1:-all}"

run_fv_python() {
  local runner=()
  if [[ -n "${FV_WINDOWS_PYTHON:-}" ]]; then
    runner=("$FV_WINDOWS_PYTHON")
  elif command -v py.exe >/dev/null 2>&1; then
    runner=(py.exe -3)
  else
    python3 "$@"
    return
  fi
  command -v wslpath >/dev/null 2>&1 || {
    echo "wslpath is required for native Windows Python" >&2
    exit 1
  }
  local arg converted=()
  for arg in "$@"; do
    if [[ "$arg" == /* ]]; then
      converted+=("$(wslpath -w "$arg")")
    else
      converted+=("$arg")
    fi
  done
  "${runner[@]}" "${converted[@]}"
}

[[ "$selection" == "all" ]] || {
  echo "usage: $(basename "$0") all" >&2
  exit 2
}

export LEAN_NUM_THREADS=1
for tool in go jq python3 rg; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "formal evidence refresh requires $tool" >&2
    exit 1
  }
done
fresh="$(mktemp -d)"
trap 'rm -rf "$fresh"' EXIT

mapfile -t circuits < <(
  jq -er '
    if .schema != "shieldd.gnark.fv_profiles.v2" then
      error("unsupported FV profile schema")
    elif (.profiles | type) != "array" then
      error("FV profile catalog must contain profiles")
    else
      [.profiles[] | select(.status == "certified") | .label]
      | if length == 0 then error("no certified profiles") else .[] end
    end
  ' "$GNARK/fv_profiles.json" | tr -d '\r'
)
[[ "${#circuits[@]}" -gt 0 ]] || {
  echo "no certified Shieldd circuits" >&2
  exit 1
}

python3 "$ROOT/scripts/gen_fv_specification_matrix.py"

for circuit in "${circuits[@]}"; do
  (
    cd "$GNARK"
    go run ./cmd/gnarkctl export-fv \
      --circuit "$circuit" \
      --sr1cs-out "$fresh/$circuit.sr1cs" \
      --manifest-out "$fresh/$circuit-manifest.json"
  )
done

FV_FRESH_DIR="$fresh" \
  "$ROOT/scripts/check-constraint-coverage.sh" \
    --refresh --require-full-deployed all

ir_args=()
for circuit in "${circuits[@]}"; do
  ir_args+=(
    "$ROOT/crates/core/component/shielded-pool/formal/$circuit-deployed-slice-ir.json"
  )
done
python3 "$GNARK/lean/gen/gen_template_inventory.py" \
  --ir "${ir_args[@]}" \
  --out "$GNARK/artifacts/certified-template-inventory.json"

python3 "$GNARK/lean/gen/gen_note_reshape_1x8_commitments.py"
python3 "$GNARK/lean/gen/gen_note_reshape_padded_spends.py"
python3 "$GNARK/lean/gen/gen_note_reshape_padded_commitments.py"
python3 "$GNARK/lean/gen/gen_note_reshape_dtk_seating.py"
python3 "$GNARK/lean/gen/gen_note_reshape_canonical_address.py"
python3 "$GNARK/lean/gen/gen_note_reshape_balance_seating.py"
python3 "$GNARK/lean/gen/gen_note_reshape_1x8_statement_seating.py"
run_fv_python "$GNARK/lean/gen/gen_template_ownership.py"

semantic_digest="$(
  run_fv_python \
    "$ROOT/scripts/fv_specification_completeness.py" \
    --emit-semantic-digest \
    | tr -d '\r'
)"
[[ "$semantic_digest" =~ ^[0-9a-f]{64}$ ]] \
  || { echo "formal refresh produced an invalid semantic digest" >&2; exit 1; }
printf '%s\n' "$semantic_digest" \
  > "$GNARK/lean/certified-protocol-semantics.sha256"

run_fv_python "$ROOT/scripts/gen-certified-circuit-artifacts.py"

echo "formal evidence refresh staged: circuits=${circuits[*]}"
