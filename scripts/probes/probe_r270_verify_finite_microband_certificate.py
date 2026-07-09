#!/usr/bin/env python3
"""#466 R270: verify the finite micro-band certificate CSV."""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path("docs/kb/data/deltastar-466-r269-finite-microband-certificate.csv"),
    )
    parser.add_argument("--micro-cutoff", type=float, default=0.755)
    parser.add_argument("--target-c", type=float, default=0.6012)
    args = parser.parse_args()

    rows = []
    failures = []
    with args.csv.open(newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            n = int(row["n"])
            p = int(row["p"])
            m = int(row["M"])
            count = int(row["count"])
            survival = count / m
            micro = survival * math.exp(args.micro_cutoff / 2.0)
            slack = args.target_c - micro
            rows.append((micro, slack, n, p, m, count))
            if slack < -1.0e-12:
                failures.append((micro, slack, n, p, m, count))

    rows.sort(reverse=True)
    print(f"R270 verify finite micro-band CSV rows={len(rows)} failures={len(failures)}")
    if rows:
        micro, slack, n, p, m, count = rows[0]
        print(
            f"worst micro={micro:.12f} slack={slack:.12f} "
            f"n={n} p={p} M={m} count={count}"
        )
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
