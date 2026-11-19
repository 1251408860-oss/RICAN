"""Compare stepwise and closed-form prediction on immutable input spans."""

import argparse
import json
import math
from pathlib import Path
import platform
from statistics import median
import time


def stepwise_view(extent, initial, limit):
    capacity = initial
    offset = min(extent, capacity - 1)
    while capacity < limit and offset == capacity - 1:
        grown = min(capacity * 2, limit)
        room = grown - offset
        offset += min(extent - offset, room - 1)
        capacity = grown
    return offset, extent - offset


def capacity_view(extent, initial, limit):
    offset = limit - 1
    return offset, extent - offset


def reads_to_handoff(initial, limit):
    count = 1
    capacity = initial
    while capacity < limit:
        capacity = min(capacity * 2, limit)
        count += 1
    return count


def span_cases(pairs):
    for initial, limit in pairs:
        for extent in (limit - 1, limit + 7, 3 * limit):
            yield extent, initial, limit


def cohorts():
    small = (
        (initial, limit)
        for limit in range(2, 129)
        for initial in range(2, limit + 1)
    )
    sampled_limits = [
        2 ** exponent + delta
        for exponent in range(8, 20)
        for delta in (-1, 0, 1)
    ] + [2 ** 20]
    large = (
        (initial, limit)
        for limit in sampled_limits
        for initial in sorted({
            2, math.isqrt(limit), limit // 4, (limit + 1) // 2, limit - 1, limit,
        })
    )
    return {"exhaustive_small": list(span_cases(small)), "dyadic_large": list(span_cases(large))}


def check_cohort(cases):
    if len(cases) != len(set(cases)):
        raise ValueError("The cohort contains duplicate spans.")
    agree = 0
    negative_detected = 0
    transitions = []
    for extent, initial, limit in cases:
        expected = stepwise_view(extent, initial, limit)
        agree += expected == capacity_view(extent, initial, limit)
        wrong_offset = limit - 2
        negative_detected += expected != (wrong_offset, extent - wrong_offset)
        transitions.append(reads_to_handoff(initial, limit))
    if agree != len(cases) or negative_detected != len(cases):
        raise ValueError("A predictor or its one-slot negative control disagrees with the expected view.")
    return {
        "cases": len(cases),
        "agree": agree,
        "negative_detected": negative_detected,
        "max_capacity": max(limit for _, _, limit in cases),
        "stepwise_read_transitions": sum(transitions),
        "max_stepwise_reads": max(transitions),
        "closed_form_simulated_reads": 0,
    }


def evaluate(predictor, cases, repeats):
    checksum = 0
    start = time.perf_counter_ns()
    for _ in range(repeats):
        for extent, initial, limit in cases:
            retained, unread = predictor(extent, initial, limit)
            checksum += retained * 31 + unread
    return (time.perf_counter_ns() - start) / (repeats * len(cases)), checksum


def run_cohort(cases, passes):
    counts = check_cohort(cases)
    repeats = math.ceil(50_000 / len(cases))
    methods = {"stepwise": stepwise_view, "capacity": capacity_view}
    for _ in range(2):
        for predictor in methods.values():
            evaluate(predictor, cases, repeats)
    samples = {name: [] for name in methods}
    for pass_index in range(passes):
        order = list(methods) if pass_index % 2 == 0 else list(reversed(methods))
        checksums = []
        for name in order:
            elapsed, checksum = evaluate(methods[name], cases, repeats)
            samples[name].append(round(elapsed, 3))
            checksums.append(checksum)
        if checksums[0] != checksums[1]:
            raise ValueError("The paired timing passes produced different view checksums.")
    return {
        **counts,
        "repeat_per_pass": repeats,
        "timed_calls_per_pass": repeats * len(cases),
        "samples_ns_per_case": samples,
        "median_ns_per_case": {name: round(median(values), 3) for name, values in samples.items()},
        "paired_median_ratio": round(median(a / b for a, b in zip(samples["stepwise"], samples["capacity"])), 4),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("build/predictor-timings.json"))
    parser.add_argument("--passes", type=int, default=21)
    args = parser.parse_args()
    if args.passes < 3:
        parser.error("--passes must be at least 3")
    results = {
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "platform": platform.system(),
        "machine": platform.machine(),
        "passes": args.passes,
        "cohorts": {name: run_cohort(cases, args.passes) for name, cases in cohorts().items()},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(args.output)


if __name__ == "__main__":
    main()
