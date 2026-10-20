#!/usr/bin/env bash
# Compile one generated contract with Solcore and run its JSON test file.
# Mirrors the pipeline of solcore's contest.sh, but takes every path from the
# environment (set by `nix develop` / `nix run .#diff`) and writes only next to
# the input file.
#
#   run-solcore.sh <dir>/<name>.json <out.json>
#
# Exit codes: 0 = runner produced <out.json> (tests may still fail),
#             3 = compilation failed (error on stderr), 4 = runner failed.
set -euo pipefail

in=$1
out=$2
: "${SOLCORE_SRC:?SOLCORE_SRC is not set (use nix develop or nix run .#diff)}"
: "${EVMONE:?EVMONE is not set (use nix develop or nix run .#diff)}"

dir=$(dirname "$in")
base=$(basename "$in" .json)
src="$dir/$base.sol"
work="$dir/$base.work"
rm -rf "$work"
mkdir -p "$work"

fail_compile() {
    cat "$1" >&2
    exit 3
}

sol-core -f "$src" --root "$dir" -i "$SOLCORE_SRC/std" -o "$work" \
    > "$work/sol-core.log" 2>&1 || fail_compile "$work/sol-core.log"
[[ -f "$work/output1.hull" ]] || fail_compile "$work/sol-core.log"

yule "$work/output1.hull" -o "$work/output.yul" \
    > "$work/yule.log" 2>&1 || fail_compile "$work/yule.log"

# The optimizer only changes gas, not return data, and dominates the run time
# on large batches; SOLC_OPTIMIZE=1 turns it back on.
solc_flags=(--strict-assembly --bin)
[[ "${SOLC_OPTIMIZE:-0}" == 1 ]] && solc_flags+=(--optimize)
solc "${solc_flags[@]}" "$work/output.yul" \
    > "$work/solc.out" 2> "$work/solc.log" || fail_compile "$work/solc.log"
tail -1 "$work/solc.out" | tr -d '\n' > "$work/output.hex"
[[ -s "$work/output.hex" ]] || fail_compile "$work/solc.log"

jq --arg s "$base" --rawfile bc "$work/output.hex" '.[$s].bytecode = $bc' "$in" \
    > "$work/runner-input.json"

testrunner "$EVMONE" "$work/runner-input.json" "$out" > "$work/testrunner.log" 2>&1 || true
if [[ ! -f "$out" ]]; then
    cat "$work/testrunner.log" >&2
    exit 4
fi
