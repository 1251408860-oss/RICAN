#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
build="$root/build/rocq"
compiler=${ROCQ:-rocq}
modules=(Reader Growth Handoff Discard)

mkdir -p "$build"
cd "$build"
for module in "${modules[@]}"; do
    cp "$root/proofs/$module.v" "$module.v"
    "$compiler" compile -q -Q . RICAN "$module.v"
done

"$compiler" check -silent -o -Q . RICAN RICAN.Discard
