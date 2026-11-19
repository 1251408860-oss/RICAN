"""Generate the signed-integer handoff agreement tasks."""

from pathlib import Path


SIGNED_MAX = 2 ** 31 - 1
CAPACITY_LIMITS = (128, 4096, 65536, 1048576, SIGNED_MAX)


def main():
    directory = Path(__file__).resolve().parent
    destination = directory.parents[1] / "build" / "cpa-inputs"
    destination.mkdir(parents=True, exist_ok=True)
    template = (directory / "reader_contract.c.in").read_text(encoding="utf-8")
    tasks = [(f"cap_{maximum}", maximum, 1) for maximum in CAPACITY_LIMITS]
    tasks.append(("negative_control_128", 128, 2))
    for name, maximum, reservation in tasks:
        source = (
            template.replace("@CAP_LIMIT@", str(maximum))
            .replace("@EXTENT_LIMIT@", str(min(3 * maximum, SIGNED_MAX)))
            .replace("@RESERVATION@", str(reservation))
        )
        (destination / f"{name}.c").write_text(source, encoding="utf-8", newline="\n")
    print(f"Wrote {len(tasks)} verification tasks to {destination}.")


if __name__ == "__main__":
    main()
