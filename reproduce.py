"""Verify the reference data and reproduce the evaluation table values."""

import argparse
import json
from pathlib import Path

from evaluation.report import method_table, native_tables, reference_data


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=root / "build")
    args = parser.parse_args()
    native, timings, verdicts = reference_data(root / "data")
    tables = native_tables(native)
    tables["table_5_methods"] = method_table(timings, verdicts)

    args.output.mkdir(parents=True, exist_ok=True)
    result = args.output / "table-values.json"
    result.write_text(json.dumps(tables, indent=2) + "\n", encoding="utf-8")
    print(f"Verified reference data and wrote the values for Tables 1-5 to {result}.")


if __name__ == "__main__":
    main()
