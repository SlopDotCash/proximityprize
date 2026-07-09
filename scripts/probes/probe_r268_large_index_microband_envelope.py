#!/usr/bin/env python3
"""#466 R268: soft large-index envelope for the micro-band cap.

R267 makes the finite branch small.  R268 asks what simple bound would suffice
for the large branch M >= 1536.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import is_prime  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import cached_desc  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[256, 512, 1024])
    parser.add_argument("--min-index", type=int, default=1536)
    parser.add_argument("--max-index", type=int, default=8000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--stride", type=int, default=1, help="test only indices M with (M-min-index) divisible by stride")
    parser.add_argument("--limit-per-n", type=int, default=0, help="0 means no per-n limit")
    args = parser.parse_args()

    rows = []
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
            s = int(np.count_nonzero(residual >= args.theta)) / m
            rows.append((s, n, p, m))
            tested_for_n += 1
            if args.limit_per_n and tested_for_n >= args.limit_per_n:
                break

    rows.sort(reverse=True)
    print(f"R268 large-index micro-band envelope cases={len(rows)} skipped={skipped}")
    print("S        n     p          M      sqrtMgap@0.39 sqrtMgap@0.40")
    print("-" * 82)
    for s, n, p, m in rows[: args.top]:
        print(
            f"{s:<8.6f} {n:<5d} {p:<10d} {m:<6d} "
            f"{(s-0.39)*math.sqrt(m):<12.6f} {(s-0.40)*math.sqrt(m):<12.6f}"
        )

    print("\nconstant caps")
    for cap in [0.406, 0.4055, 0.405, 0.404, 0.403, 0.402]:
        viol = [row for row in rows if row[0] > cap]
        print(f"cap={cap:.4f} violations={len(viol)} worst_excess={(max((r[0]-cap for r in rows), default=0.0)):.6f}")

    print("\nfit caps S <= base + a/sqrt(M)")
    for base in [0.38, 0.385, 0.39, 0.395, 0.40]:
        req = max((s - base) * math.sqrt(m) for s, _n, _p, m in rows)
        arg = max(rows, key=lambda r: (r[0] - base) * math.sqrt(r[3]))
        print(f"base={base:.3f} a_req={req:.6f} arg n={arg[1]} p={arg[2]} M={arg[3]} S={arg[0]:.6f}")

    print("\nfit caps S <= base + a/log(M)")
    for base in [0.38, 0.385, 0.39, 0.395, 0.40]:
        req = max((s - base) * math.log(m) for s, _n, _p, m in rows)
        arg = max(rows, key=lambda r: (r[0] - base) * math.log(r[3]))
        print(f"base={base:.3f} a_req={req:.6f} arg n={arg[1]} p={arg[2]} M={arg[3]} S={arg[0]:.6f}")


if __name__ == "__main__":
    main()
