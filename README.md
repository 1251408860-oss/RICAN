# RICAN

Companion artifact for *Final-Capacity Equivalence for Growing Line Readers*. RICAN proves that a full growing line read and one read at the final capacity produce the same retained and unread byte lists. The artifact includes the Rocq proof, the synthetic handoff comparison, and the reference data for the evaluation.

## Repository Navigation

| Paper component | What to inspect | Artifact |
| --- | --- | --- |
| Bounded reader and resize invariant, Sections 2–3 | Ordered transfer, the reserved terminator slot, and the payload budget of each resize | [Reader.v](proofs/Reader.v) · [Growth.v](proofs/Growth.v) |
| Final-capacity equivalence and discard law, Section 3 | Exact list split, equality of the selected continuation, and the guarded last index | [Handoff.v](proofs/Handoff.v) · [Discard.v](proofs/Discard.v) |
| Native comparisons, Tables 1–4 | Cohort counts, matched continuation lengths, and release-pair outcomes | [Native observations](data/native-observations.json) |
| Method-level comparison, Table 5 | Stepwise and closed-form predictors, paired timing samples, and symbolic agreement tasks | [Predictors](evaluation/predictors.py) · [Timing data](data/predictor-timings.json) · [Verification](evaluation/verification) |
| Reproduction | Reference data validation and table values | [reproduce.py](reproduce.py) · [Reference checksums](data/SHA256SUMS) |

## Environment

| Workflow | Requirements |
| --- | --- |
| Reproduce the table values and run the predictor benchmark | Python 3.12 standard library |
| Check the proofs | Rocq 9.1.1 with its standard library and Bash |
| Verify the signed-integer model | Linux or WSL with Bash, GNU `timeout`, Java 21, and [CPAchecker 4.2.2](https://doi.org/10.5281/zenodo.17777566) |

## Bundled Reference Data

| Comparison | Reference result |
| --- | ---: |
| Reader-only observations matching the model | 173,808 / 173,808 |
| Native parser traces matching the model | 4,224 / 4,224 |
| Fixed- and growing-heap pairs with identical projected continuations | 528 / 528 |
| Matched release pairs with prefix agreement | 2,112 / 2,112 |
| Synthetic handoff views on which both predictors agree | 25,050 / 25,050 |

Tables 1–4 use aggregate observations of the native runs. The timing columns in Table 5 use 21 paired samples per cohort, collected with CPython 3.12.10 on Windows. The verifier snapshot records five agreement domains and one off-by-one control for each configuration. [Verifier results](data/verifier-results.tsv)

## Quick Start

Run this command from the repository root.

```bash
python reproduce.py
```

The command verifies the reference checksums, re-evaluates the 25,050 synthetic views, and writes the values for Tables 1–5 to `build/table-values.json`.

## Check the Rocq Proofs

```bash
bash proofs/check.sh
```

The script compiles the four modules and recursively checks `RICAN.Discard`. The paper's main statements are `final_capacity_equivalence`, `discard_capacity_law`, and `discard_last_index`. Set `ROCQ` to the path to the Rocq executable if needed.

## Rerun the Method-Level Experiment

Run fresh prediction timings with `python -m evaluation.predictors`. The command alternates the run order across 21 paired passes and writes `build/predictor-timings.json`. Timings depend on the host.

Generate the signed-integer tasks and invoke the two CPAchecker configurations with the commands below.

```bash
python evaluation/verification/prepare.py
bash evaluation/verification/run.sh /path/to/CPAchecker-4.2.2-unix/bin/cpachecker
```

The runner writes verdicts, exit statuses, and wall times to `build/cpachecker/results.tsv`. The off-by-one task checks that the verifier rejects an intentionally different split. Each task has a 45-second CPU limit. A time-limited `kInduction` result can vary across runs.

## Citation

If you use this artifact, cite the companion manuscript, *Final-Capacity Equivalence for Growing Line Readers*.
