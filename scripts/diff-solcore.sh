#!/usr/bin/env bash
# Differential test of the Lean ABI model against Solcore. All arguments are
# passed to `abidiff` (see `lake exe abidiff --help`).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build abidiff >&2
exec lake exe abidiff "$@"
