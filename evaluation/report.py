"""Validate reference observations and derive the paper's table values."""

import csv
from hashlib import sha256
import json
from math import isfinite
from statistics import median

from evaluation.predictors import check_cohort, cohorts


REFERENCE_FILES = {
    "native-observations.json",
    "predictor-timings.json",
    "verifier-results.tsv",
}


def verify_inputs(directory):
    entries = (directory / "SHA256SUMS").read_text(encoding="ascii").splitlines()
    expected = {}
    for entry in entries:
        digest, name = entry.split("  ", 1)
        if name in expected:
            raise ValueError(f"Duplicate reference file in SHA256SUMS: {name}")
        expected[name] = digest
    if set(expected) != REFERENCE_FILES:
        raise ValueError("SHA256SUMS must list the three reference inputs.")
    for name, digest in expected.items():
        if sha256((directory / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"Reference data checksum mismatch: {name}")


def reference_data(directory):
    verify_inputs(directory)
    native = json.loads((directory / "native-observations.json").read_text(encoding="utf-8"))
    timings = json.loads((directory / "predictor-timings.json").read_text(encoding="utf-8"))
    with (directory / "verifier-results.tsv").open(encoding="utf-8", newline="") as stream:
        verdicts = list(csv.DictReader(stream, delimiter="\t"))
    return native, timings, verdicts


def depth_total(histogram):
    return sum(int(depth) * count for depth, count in histogram.items())


def native_tables(native):
    counts = native["cohorts"]
    pairs = native["fixed_growth"]
    compilers = native["toolchains"]
    growth = native["growth_schedules"]
    releases = native["release_comparison"]
    depths = releases["runs_by_continuation_length"]
    extensions = releases["pairs_by_additional_corrected_events"]
    checks = {
        "fixed/growing histogram": sum(pairs["pairs_by_shared_continuation_length"].values()) == pairs["pairs"],
        "fixed/growing release groups": sum(row["pairs"] for row in pairs["reports"].values()) == pairs["pairs"],
        "full parser traces": sum(row["trace_matches"] for row in compilers) == counts["native_parser"]["matches"],
        "parser cohort size": sum(2 * row["runs_per_release"] for row in compilers) == counts["native_parser"]["observations"],
        "growth subset": sum(row["matching_classifications"] for row in growth) == counts["reallocation_enabled"]["matches"],
        "matched release count": all(sum(hist.values()) == releases["pairs"] for hist in depths.values()),
        "additional records": depth_total(depths["r63"]) - depth_total(depths["r62"]) == depth_total(extensions),
        "release pair outcomes": sum(extensions.values()) == releases["pairs"],
    }
    for name, valid in checks.items():
        if not valid:
            raise ValueError(f"Inconsistent native aggregate: {name}")
    return {
        "table_1_cohorts": counts,
        "table_2_fixed_growth": pairs,
        "table_3_toolchains": compilers,
        "table_4_growth_schedules": growth,
        "release_comparison": releases,
        "storage_control": native["storage_control"],
        "compiler_control": native["compiler_control"],
    }


def method_table(timings, verdicts):
    cohorts_checked = []
    for name, cases in cohorts().items():
        counts = check_cohort(cases)
        saved = timings["cohorts"][name]
        if any(saved[key] != value for key, value in counts.items()):
            raise ValueError(f"Synthetic workload differs from the reference cohort: {name}")
        samples = saved["samples_ns_per_case"]
        stepwise, closed_form = samples["stepwise"], samples["capacity"]
        for values in (stepwise, closed_form):
            if len(values) != timings["passes"] or any(not isfinite(value) or value <= 0 for value in values):
                raise ValueError(f"Invalid timing samples in cohort: {name}")
        cohorts_checked.append({
            "name": name,
            **counts,
            "stepwise_ns": median(stepwise),
            "closed_form_ns": median(closed_form),
            "paired_ratio": median(a / b for a, b in zip(stepwise, closed_form)),
        })

    configurations = ("predicateAnalysis", "kInduction")
    domains = {"cap_128", "cap_4096", "cap_65536", "cap_1048576", "cap_2147483647"}
    if {row["configuration"] for row in verdicts} != set(configurations):
        raise ValueError("Verifier results must cover the two configurations.")
    verifier_summary = {}
    for configuration in configurations:
        selected = [row for row in verdicts if row["configuration"] == configuration]
        agreement = [row for row in selected if row["test"] in domains]
        control = [row["verdict"] for row in selected if row["test"] == "negative_control_128"]
        if len(selected) != len(domains) + 1 or {row["test"] for row in agreement} != domains or control != ["FALSE"]:
            raise ValueError(f"Verifier domain coverage or negative control differs for {configuration}.")
        seconds = [int(row["wall_ms"]) / 1000 for row in agreement]
        verifier_summary[configuration] = {
            "proved": sum(row["verdict"] == "TRUE" for row in agreement),
            "domains": len(agreement),
            "wall_seconds": [min(seconds), max(seconds)],
            "negative_control": control[0],
        }

    return {
        "total_views": sum(cohort["cases"] for cohort in cohorts_checked),
        "matching_views": sum(cohort["agree"] for cohort in cohorts_checked),
        "stepwise_read_transitions": sum(cohort["stepwise_read_transitions"] for cohort in cohorts_checked),
        "max_stepwise_reads": max(cohort["max_stepwise_reads"] for cohort in cohorts_checked),
        "predictors": cohorts_checked,
        "verifiers": verifier_summary,
    }
