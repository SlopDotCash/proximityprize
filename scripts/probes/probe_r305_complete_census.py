#!/usr/bin/env python3
"""#466 R305c: COMPLETE census of the depth-3 bad-prime set for n = 2^k.

Every bad prime (nonzero depth-3 excess) divides |Norm(z)| for some nonzero difference z of
two char-0 3-sum vectors.  This probe enumerates ALL difference classes, computes their exact
cyclotomic norms, factors them (Pollard rho), and runs the exact grouped evaluator at every
candidate prime ≡ 1 (mod n) — producing the complete table {(p, excess(p))} for ALL p, with
exact-Wick violations (excess > 45n^2 - 40n) flagged.  No range limit: the census is total.
"""

from __future__ import annotations

import argparse
import math
import random
import sys
from collections import defaultdict

import numpy as np


def build_n3(n: int) -> tuple[np.ndarray, np.ndarray]:
    m = n // 2
    N3: dict[tuple[int, ...], int] = defaultdict(int)
    for a in range(n):
        sa, ia = (1, a) if a < m else (-1, a - m)
        for b in range(n):
            sb, ib = (1, b) if b < m else (-1, b - m)
            for c in range(n):
                sc, ic = (1, c) if c < m else (-1, c - m)
                v = [0] * m
                v[ia] += sa
                v[ib] += sb
                v[ic] += sc
                N3[tuple(v)] += 1
    keys = np.array(list(N3.keys()), dtype=np.int8)
    cnts = np.array([N3[tuple(k)] for k in keys], dtype=np.int64)
    return keys, cnts


def distinct_differences(keys: np.ndarray) -> np.ndarray:
    """All distinct nonzero differences keys[j] - keys[i] (as int8 rows)."""
    K, m = keys.shape
    seen = set()
    for i in range(K):
        diffs = keys - keys[i]
        for row in diffs.view(f"V{m}").ravel():
            seen.add(row.tobytes())
    zero = bytes(m)
    seen.discard(zero)
    out = np.frombuffer(b"".join(sorted(seen)), dtype=np.int8).reshape(-1, m)
    return out


def norms_of(zs: np.ndarray, n: int) -> np.ndarray:
    m = n // 2
    val = np.ones(len(zs), dtype=np.complex128)
    zf = zs.astype(np.float64)
    for u in range(1, n, 2):
        roots = np.exp(2j * np.pi * u * np.arange(m) / n)
        val *= zf @ roots
    return np.rint(val.real).astype(np.int64)


def is_probable_prime(x: int) -> bool:
    if x < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % p == 0:
            return x == p
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        y = pow(a, d, x)
        if y in (1, x - 1):
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def pollard_rho(x: int) -> int:
    if x % 2 == 0:
        return 2
    while True:
        c = random.randrange(1, x)
        f = lambda t: (t * t + c) % x
        a = b = random.randrange(2, x)
        d = 1
        while d == 1:
            a = f(a)
            b = f(f(b))
            d = math.gcd(abs(a - b), x)
        if d != x:
            return d


def factorize(x: int) -> list[int]:
    if x == 1:
        return []
    if is_probable_prime(x):
        return [x]
    d = pollard_rho(x)
    return factorize(d) + factorize(x // d)


def exact_excess(p: int, n: int, keys: np.ndarray, cnts: np.ndarray, e3_char0: int) -> int:
    m = n // 2
    g0 = None
    for g in range(2, p):
        cand = pow(g, (p - 1) // n, p)
        if pow(cand, n // 2, p) != 1:
            g0 = cand
            break
    assert g0 is not None
    powers = np.empty(m, dtype=np.int64)
    x = 1
    for j in range(m):
        powers[j] = x
        x = x * g0 % p
    evals = (keys.astype(np.int64) @ powers) % p
    order = np.argsort(evals, kind="stable")
    ev_sorted = evals[order]
    ct_sorted = cnts[order]
    boundaries = np.nonzero(np.diff(ev_sorted))[0] + 1
    group_sums = np.add.reduceat(ct_sorted, np.concatenate(([0], boundaries)))
    return int(np.sum(group_sums**2)) - e3_char0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=32)
    args = ap.parse_args()
    n = args.n
    headroom = 45 * n**2 - 40 * n

    keys, cnts = build_n3(n)
    e3_char0 = int(np.sum(cnts**2))
    print(f"n={n}: K={len(keys)} vectors, char0={e3_char0}, headroom={headroom}", flush=True)

    zs = distinct_differences(keys)
    print(f"{len(zs)} distinct nonzero difference classes", flush=True)

    norms = np.abs(norms_of(zs, n))
    assert np.all(norms != 0), "zero norm on nonzero class"
    distinct_norms = sorted(set(int(v) for v in norms))
    print(f"{len(distinct_norms)} distinct |Norm| values, max={max(distinct_norms):.3e}",
          flush=True)

    candidates: set[int] = set()
    for nv in distinct_norms:
        for p in set(factorize(nv)):
            if p % n == 1:
                candidates.add(p)
    print(f"{len(candidates)} candidate primes ≡ 1 mod {n} dividing some norm", flush=True)

    rows = []
    for p in sorted(candidates):
        exc = exact_excess(p, n, keys, cnts, e3_char0)
        if exc:
            rows.append((p, exc))
    print(f"\nCOMPLETE bad-prime table for n={n} ({len(rows)} primes with nonzero excess, "
          f"ALL beta):", flush=True)
    quantum = 0
    for p, exc in rows:
        beta = math.log(p) / math.log(n)
        quantum = math.gcd(quantum, exc)
        print(f"  p={p:>14} beta={beta:.3f} excess={exc}"
              + ("  *** EXACT-WICK VIOLATION" if exc > headroom else ""), flush=True)
    viol = [(p, e) for p, e in rows if e > headroom]
    print(f"\nexact-Wick violations: {len(viol)}; largest violating prime: "
          f"{max(viol)[0] if viol else None} "
          f"(beta={math.log(max(viol)[0])/math.log(n):.3f})" if viol else "none", flush=True)
    print(f"excess quantum (gcd over all bad primes): {quantum}", flush=True)
    print(f"largest bad prime overall: p={rows[-1][0]} "
          f"beta={math.log(rows[-1][0])/math.log(n):.3f}" if rows else "no bad primes",
          flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
