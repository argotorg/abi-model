#!/usr/bin/env bash
# Compile one generated contract with solcore-rs and run its calls on Anvil.
#
#   run-solcore-rs.sh <dir>/<name>/main.sol <calls> <out.jsonl>
#
# <calls> holds one hex calldata per line (no 0x). For each line, <out.jsonl>
# gets one JSON object {"status": "success" | "revert", "returndata": "<hex>"}.
#
# Environment:
#   ABIDIFF_RPC    JSON-RPC URL of a running Anvil (started by `abidiff`)
#   SOLCORE        solcore-rs compiler binary (default: `solcore` on PATH)
#   SOLCORE_STD    std library root (default: the compiler's own resolution)
#   SOLC_OPTIMIZE  1 to run the solc optimizer (slower, only changes gas)
#   EVM_VERSION    target EVM (default: osaka, as solcore-rs's E2E tests)
#
# Exit codes: 0 = calls ran (they may still revert), 3 = compilation failed
# (diagnostics on stderr), 4 = runner error, 5 = deployment failed.
set -euo pipefail

src=$1
calls=$2
out=$3
: "${ABIDIFF_RPC:?ABIDIFF_RPC is not set (abidiff starts Anvil and sets it)}"
solcore=${SOLCORE:-solcore}
evm=${EVM_VERSION:-osaka}

work="$(dirname "$src")/work"
rm -rf "$work"
mkdir -p "$work"

fail_compile() {
    cat "$1" >&2
    exit 3
}

std_args=()
[[ -n "${SOLCORE_STD:-}" ]] && std_args=(--std-root "$SOLCORE_STD")

"$solcore" "$src" "${std_args[@]}" --color never --emit-yul="$work/output.yul" \
    > "$work/solcore.log" 2>&1 || fail_compile "$work/solcore.log"
[[ -s "$work/output.yul" ]] || fail_compile "$work/solcore.log"

solc_flags=(--strict-assembly --evm-version "$evm" --bin)
[[ "${SOLC_OPTIMIZE:-0}" == 1 ]] && solc_flags+=(--optimize)
solc "${solc_flags[@]}" "$work/output.yul" \
    > "$work/solc.out" 2> "$work/solc.log" || fail_compile "$work/solc.log"
bytecode=$(grep -E '^[0-9a-fA-F]+$' "$work/solc.out" | tail -1 || true)
[[ -n "$bytecode" ]] || fail_compile "$work/solc.log"

rpc() {
    # rpc <method> <params-json>
    curl -sS --fail --max-time 60 -H 'Content-Type: application/json' \
        --data "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"$1\",\"params\":$2}" \
        "$ABIDIFF_RPC"
}

# Anvil's first account is unlocked, so it can send unsigned transactions.
gas=0xffffff # below the EIP-7825 per-transaction cap of osaka
from=$(rpc eth_accounts '[]' | jq -er '.result[0]') || {
    echo "cannot reach Anvil at $ABIDIFF_RPC" >&2
    exit 4
}
tx=$(rpc eth_sendTransaction \
    "[{\"from\":\"$from\",\"data\":\"0x$bytecode\",\"gas\":\"$gas\"}]") || exit 4
echo "$tx" > "$work/deploy.json"
hash=$(jq -r '.result // empty' <<< "$tx")
if [[ -z "$hash" ]]; then
    echo "deployment rejected: $(jq -c '.error' <<< "$tx")" >&2
    exit 5
fi
receipt=$(rpc eth_getTransactionReceipt "[\"$hash\"]") || exit 4
echo "$receipt" >> "$work/deploy.json"
if [[ $(jq -r '.result.status' <<< "$receipt") != 0x1 ]]; then
    echo "deployment reverted" >&2
    exit 5
fi
addr=$(jq -r '.result.contractAddress' <<< "$receipt")

: > "$out"
while IFS= read -r data || [[ -n "$data" ]]; do
    [[ -z "$data" ]] && continue
    resp=$(rpc eth_call \
        "[{\"from\":\"$from\",\"to\":\"$addr\",\"data\":\"0x$data\",\"gas\":\"$gas\"},\"latest\"]") \
        || exit 4
    # success: {"result": "0x…"}; revert: {"error": {"data": "0x…", …}}
    jq -c 'if has("result")
             then {status: "success", returndata: (.result | ltrimstr("0x"))}
             else {status: "revert", returndata: ((.error.data // "0x") | ltrimstr("0x")),
                   message: (.error.message // "")}
           end' <<< "$resp" >> "$out"
done < "$calls"
