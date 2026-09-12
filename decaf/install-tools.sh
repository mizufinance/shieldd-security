#!/usr/bin/env bash
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends python3 git gcc libc6-dev curl ca-certificates gdb binutils
export CARGO_HOME=/opt/decaf/cargo RUSTUP_HOME=/opt/decaf/rustup
if [[ ! -x "$CARGO_HOME/bin/rustc" ]]; then
  curl --fail --location --proto '=https' --tlsv1.2 https://sh.rustup.rs -o /tmp/decaf-rustup.sh
  sh /tmp/decaf-rustup.sh -y --profile minimal --default-toolchain 1.90.0 --no-modify-path
fi
if [[ ! -x /opt/decaf/go/bin/go ]]; then
  curl --fail --location https://go.dev/dl/go1.25.4.linux-amd64.tar.gz -o /tmp/decaf-go.tar.gz
  echo '9fa5ffeda4170de60f67f3aa0f824e426421ba724c21e133c1e35d6159ca1bec  /tmp/decaf-go.tar.gz' | sha256sum --check
  tar -xzf /tmp/decaf-go.tar.gz -C /opt/decaf
  rm /tmp/decaf-go.tar.gz
fi
