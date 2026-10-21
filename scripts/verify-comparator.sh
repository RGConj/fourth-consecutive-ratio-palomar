#!/usr/bin/env bash
set -euo pipefail

# Adapted from PalomarRegistry/PalomarTemplate/scripts/verify-comparator.sh
# (Apache-2.0). The judged configuration remains comparator.json; the temporary
# copy registers the toolchain's independent kernels, matching Palomar policy.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for command in bwrap lake lean python3; do
  command -v "$command" >/dev/null 2>&1 || {
    echo "error: missing required command: $command" >&2
    exit 1
  }
done

prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || {
    echo "error: the selected toolchain does not bundle $tool" >&2
    exit 1
  }
done

config=$(mktemp "${TMPDIR:-/tmp}/fourth-ratio-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if not isinstance(config, dict) or "external_kernels" in config:
    raise SystemExit("Invalid submission Comparator configuration")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake exe cache get
lake comparator --config "$config"
