#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
    printf 'Usage: bash evaluation/verification/run.sh /path/to/bin/cpachecker\n' >&2
    exit 2
fi

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
tool=$(realpath "$1")
inputs="$root/build/cpa-inputs"
outputs="$root/build/cpachecker"
tasks=(cap_128 cap_4096 cap_65536 cap_1048576 cap_2147483647 negative_control_128)

for task in "${tasks[@]}"; do
    if [[ ! -f "$inputs/$task.c" ]]; then
        printf 'Generate the tasks with python evaluation/verification/prepare.py.\n' >&2
        exit 2
    fi
done
mkdir -p "$outputs"
bash "$tool" --version >"$outputs/version.txt" 2>&1

run_check() {
    local configuration=$1 task=$2
    local result_dir="$outputs/$configuration-$task"
    local start end status verdict
    start=$(date +%s%N)
    status=0
    timeout --kill-after=5s 60s bash "$tool" "--$configuration" \
        --heap 1536M --timelimit 45s --stats \
        --spec "$here/reader_property.prp" --output-path "$result_dir" \
        "$inputs/$task.c" >"$result_dir.log" 2>&1 || status=$?
    end=$(date +%s%N)
    verdict=$(sed -nE 's/^[[:space:]]*Verification result: (TRUE|FALSE|UNKNOWN).*/\1/p' \
        "$result_dir.log" | sed -n '1p')
    if [[ -z "$verdict" ]]; then
        case "$status" in
            124|137) verdict=TIMEOUT ;;
            *) verdict=ERROR ;;
        esac
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$configuration" "$task" "$verdict" \
        "$status" "$(((end - start) / 1000000))" | tee -a "$outputs/results.tsv"
}

printf 'configuration\ttest\tverdict\texit_status\twall_ms\n' >"$outputs/results.tsv"
for configuration in predicateAnalysis kInduction; do
    for task in "${tasks[@]}"; do
        run_check "$configuration" "$task"
    done
done
if grep -q $'\tERROR\t' "$outputs/results.tsv"; then
    printf 'A verifier invocation failed. See the logs in %s.\n' "$outputs" >&2
    exit 1
fi
