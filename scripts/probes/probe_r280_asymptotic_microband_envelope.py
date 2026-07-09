#!/usr/bin/env python3
"""#466 R280: asymptotic-envelope search for the remaining micro-band branch.

After R278, the open branch is `M >= 8001`.  This probe searches for simple
large-index envelope shapes for `S(0.75)` and q60.  The point is not to certify
a sampled theorem, but to identify a plausible analytic target with enough
slack to be worth formalizing.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import is_prime  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import cached_desc  # noqa: E402


@dataclass(frozen=True)
class Row:
    n: int
    p: int
    m: int
    survival: float
    q60: float
    q625: float
    q65: float


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[256, 512, 1024])
    parser.add_argument("--min-index", type=int, default=8001)
    parser.add_argument("--max-index", type=int, default=100000)
    parser.add_argument("--stride", type=int, default=17)
    parser.add_argument("--limit-per-n", type=int, default=0)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--top", type=int, default=20)
    args = parser.parse_args()

    rows: list[Row] = []
    skipped = 0
    for n in args.ns:
        tested_for_n = 0
        for m in range(args.min_index, args.max_index + 1):
            if (m - args.min_index) % args.stride != 0:
                continue
            p = m * n + 1
            if not is_prime(p):
                continue
            cached = cached_desc(p, n, args.chunk, args.cache_dir, args.cache_only)
            if cached is None:
                skipped += 1
                continue
            _xs, desc = cached
            residual = desc[min(args.trim, len(desc)) :]
            rows.append(
                Row(
                    n=n,
                    p=p,
                    m=m,
                    survival=int(np.count_nonzero(residual >= args.theta)) / m,
                    q60=float(np.quantile(residual, 0.60)),
                    q625=float(np.quantile(residual, 0.625)),
                    q65=float(np.quantile(residual, 0.65)),
                )
            )
            tested_for_n += 1
            if args.limit_per_n and tested_for_n >= args.limit_per_n:
                break

    print(
        f"R280 asymptotic micro-band envelope cases={len(rows)} skipped={skipped} "
        f"range=[{args.min_index},{args.max_index}] stride={args.stride}"
    )
    if not rows:
        return

    print("\nfrontier by S(0.75)")
    print("S075     q60      q625     q65      sqrtGap@.39 sqrtGap@.395 n     p          M")
    print("-" * 104)
    for row in sorted(rows, key=lambda r: r.survival, reverse=True)[: args.top]:
        print(
            f"{row.survival:<8.6f} {row.q60:<8.6f} {row.q625:<8.6f} {row.q65:<8.6f} "
            f"{(row.survival - 0.39) * math.sqrt(row.m):<12.6f} "
            f"{(row.survival - 0.395) * math.sqrt(row.m):<12.6f} "
            f"{row.n:<5d} {row.p:<10d} {row.m}"
        )

    print("\nfrontier by q60")
    print("q60      S075     q625     q65      sqrtGap@.70 sqrtGap@.72  n     p          M")
    print("-" * 104)
    for row in sorted(rows, key=lambda r: r.q60, reverse=True)[: args.top]:
        print(
            f"{row.q60:<8.6f} {row.survival:<8.6f} {row.q625:<8.6f} {row.q65:<8.6f} "
            f"{(row.q60 - 0.70) * math.sqrt(row.m):<12.6f} "
            f"{(row.q60 - 0.72) * math.sqrt(row.m):<12.6f} "
            f"{row.n:<5d} {row.p:<10d} {row.m}"
        )

    def report_metric(name: str, getter) -> None:
        print(f"\n{name} envelope fits")
        vals = [(getter(row), row) for row in rows]
        row_max = max(vals, key=lambda vr: vr[0])[1]
        print(
            f"max={getter(row_max):.8f} n={row_max.n} p={row_max.p} M={row_max.m} "
            f"S={row_max.survival:.8f} q60={row_max.q60:.8f}"
        )
        for base in ([0.385, 0.39, 0.395, 0.40] if name == "S075" else [0.68, 0.70, 0.72, 0.74]):
            arg = max(rows, key=lambda r: (getter(r) - base) * math.sqrt(r.m))
            req = (getter(arg) - base) * math.sqrt(arg.m)
            print(
                f"sqrt cap base={base:.3f} a_req={req:.6f} "
                f"arg n={arg.n} p={arg.p} M={arg.m} value={getter(arg):.8f}"
            )
        for base in ([0.385, 0.39, 0.395, 0.40] if name == "S075" else [0.68, 0.70, 0.72, 0.74]):
            arg = max(rows, key=lambda r: (getter(r) - base) * math.log(r.m))
            req = (getter(arg) - base) * math.log(arg.m)
            print(
                f"log cap  base={base:.3f} a_req={req:.6f} "
                f"arg n={arg.n} p={arg.p} M={arg.m} value={getter(arg):.8f}"
            )

    report_metric("S075", lambda r: r.survival)
    report_metric("q60", lambda r: r.q60)

    print("\nconstant caps by dyadic M bucket")
    buckets: dict[int, list[Row]] = {}
    for row in rows:
        buckets.setdefault(row.m.bit_length() - 1, []).append(row)
    print("bucket        cases maxS      maxq60    maxq625   maxq65")
    print("-" * 72)
    for b in sorted(buckets):
        rs = buckets[b]
        print(
            f"[2^{b},2^{b+1}) {len(rs):<5d} "
            f"{max(r.survival for r in rs):<9.6f} {max(r.q60 for r in rs):<9.6f} "
            f"{max(r.q625 for r in rs):<9.6f} {max(r.q65 for r in rs):<9.6f}"
        )


if __name__ == "__main__":
    main()
