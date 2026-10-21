#!/usr/bin/env bash
# Fail-closed reproduction on Linux, including sandboxed independent replay.
set -Eeuo pipefail
cd "$(dirname "$0")/.."
OUT=${1:-logs/repro}
mkdir -p "$OUT"
run() {
  local name=$1; shift
  printf "Running %s\n" "$name"
  "$@" 2>&1 | tee "$OUT/$name.log"
}
run sources python3 scripts/check_sources.py
run cache lake exe cache get
run build lake build
run metadata python3 scripts/check_metadata.py
for gate in scripts/Check*Axioms.lean; do
  run "$(basename "$gate" .lean)" lake env lean "$gate"
done
run comparator bash scripts/verify-comparator.sh
printf "All reproduction gates passed.\n"
