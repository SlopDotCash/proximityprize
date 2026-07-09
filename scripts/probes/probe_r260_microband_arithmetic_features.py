#!/usr/bin/env python3
"""#466 R260: arithmetic features of the trim-five micro-band obstruction.

R259 says the micro-band cap should be attacked directly:

    S(0.75) <= 612/1485

on the main lane.  This probe mines arithmetic features of the worst rows to
see whether the obstruction clusters in a recognizable subfamily of indices M
or primes p = M*n + 1.
"""

from __future__ import annotations

import argparse
import math
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import factor  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def omega(n: int) -> int:
    return len(factor(n))


def largest_prime_factor(n: int) -> int:
    fs = factor(n)
    return max(fs) if fs else 1


def v2(n: int) -> int:
    out = 0
    while n and n % 2 == 0:
        out += 1
        n //= 2
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-min-a", type=int, default=8)
    parser.add_argument("--medium-max-a", type=int, default=10)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    cases = medium_cases(
        args.medium_min_a,
        args.medium_max_a,
        args.medium_max_index,
        args.min_index,
        args.chunk,
        args.cache_dir,
        args.cache_only,
    )

    rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        s075 = int(np.count_nonzero(residual >= args.theta)) / case.m
        micro = s075 * math.exp(0.755 / 2.0)
        M = case.m
        p = case.p
        rows.append(
            (
                micro,
                s075,
                case.n,
                p,
                M,
                M % 3,
                M % 5,
                M % 7,
                M % 8,
                M % 16,
                v2(M - 1),
                v2(M + 1),
                omega(M),
                largest_prime_factor(M),
                omega(M - 1),
                omega(M + 1),
                p % 3,
                p % 5,
                p % 7,
                p % 16,
            )
        )
    rows.sort(reverse=True)

    print(f"R260 micro-band arithmetic features cases={len(rows)} trim={args.trim} theta={args.theta}")
    print("micro    S075     n     p          M      Mmod16 v2M-1 v2M+1 omegaM lpfM  omegaM-1 omegaM+1")
    print("-" * 118)
    for row in rows[: args.top]:
        (
            micro,
            s075,
            n,
            p,
            M,
            _m3,
            _m5,
            _m7,
            _m8,
            m16,
            v2m1,
            v2p1,
            om,
            lpf,
            omm1,
            omp1,
            *_,
        ) = row
        print(
            f"{micro:<8.6f} {s075:<8.6f} {n:<5d} {p:<10d} {M:<6d} "
            f"{m16:<6d} {v2m1:<6d} {v2p1:<6d} {om:<6d} {lpf:<5d} {omm1:<8d} {omp1}"
        )

    print("\nfeature correlations with micro")
    names = [
        "M",
        "M/n",
        "logM",
        "Mmod3",
        "Mmod5",
        "Mmod7",
        "Mmod8",
        "Mmod16",
        "v2(M-1)",
        "v2(M+1)",
        "omegaM",
        "lpfM",
        "omegaM-1",
        "omegaM+1",
        "pmod3",
        "pmod5",
        "pmod7",
        "pmod16",
    ]
    matrix = []
    target = []
    for row in rows:
        micro, _s075, n, p, M = row[:5]
        target.append(micro)
        matrix.append([M, M / n, math.log(M), *row[5:]])
    matrix_np = np.array(matrix, dtype=float)
    target_np = np.array(target, dtype=float)
    scored = []
    for idx, name in enumerate(names):
        corr = float(np.corrcoef(target_np, matrix_np[:, idx])[0, 1])
        scored.append((abs(corr), name, corr))
    for _abs, name, corr in sorted(scored, reverse=True):
        print(f"{name:<10s} {corr:+.6f}")

    print("\nresidue enrichment among top rows")
    for topk in [20, 50, 100]:
        subset = rows[:topk]
        print(f"top{topk}")
        for modulus in [3, 5, 7, 8, 16]:
            counts = Counter(row[4] % modulus for row in subset)
            common = " ".join(f"{r}:{c}" for r, c in counts.most_common(4))
            print(f"  M mod {modulus}: {common}")

    print("\nworst by n")
    by_n = defaultdict(list)
    for row in rows:
        by_n[row[2]].append(row)
    for n, vals in sorted(by_n.items()):
        best = vals[0]
        print(f"n={n} micro={best[0]:.8f} S075={best[1]:.8f} p={best[3]} M={best[4]}")


if __name__ == "__main__":
    main()
