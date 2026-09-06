#!/usr/bin/env python3
"""SW1 lane ARC probe: exact max-window (arc/AP) occupancy profile of every dilate of mu_n.

Object.  For a prime p = 1 (mod n) let mu_n = {x in F_p^* : x^n = 1}.  For a dilation b and a
window length L define

    T_b(L) = max_a |b*mu_n  cap  [a, a+L)|        (cyclic windows in Z/p),

and the CLT-normalized excess

    R(L) = ( max_b T_b(L) - n*L/p ) / sqrt(n * ln(p/n)).

The doctrine's missing ingredient (brief form (F)) is R(L) <= C for every L with an absolute C.
Because b*mu_n = b'*mu_n whenever b/b' in mu_n, `max_b` is a max over the m = (p-1)/n cosets
g^i * mu_n, i < m, which we enumerate EXACTLY when m is small enough and SAMPLE otherwise (the
report says which).  AP form: an AP of difference d and length L meets b*mu_n in exactly the
same count as the interval of length L meets (b/d)*mu_n, so the max over all APs of length L
equals max_b T_b(L); nothing is lost by using intervals.

All arithmetic is exact (numpy int64; modular products use a 16-bit split so p < 2^33 is safe).
The sliding-window maximum of one coset is O(n log n) via searchsorted on the sorted coset
concatenated with its p-shift (cyclic windows).

Baseline.  For comparison we run the same statistic on uniformly random n-subsets of Z/p (the
"random model"), with the same number of samples as cosets examined, so the two maxima are
comparable order statistics.

Output.  Per (n, p): a table over a log grid of L.  Summary: worst R over L, where it sits.
PASS iff every measured R(L) <= R_MAX (a calibration threshold, NOT a proof of anything).
Deterministic (fixed seed).  Exit code 1 on FAIL.

Usage:  python3 sw1_arc_max_ap_profile.py [--fast]
"""
import math
import os
import sys
import time

import numpy as np
from sympy import isprime, primitive_root

R_MAX = 4.0
SEED = 20260905

FAST = "--fast" in sys.argv


def primes_congruent_near(n, count, start):
    """count primes p = 1 (mod n) with p >= start, ascending."""
    out = []
    p = start - ((start - 1) % n)  # p = 1 mod n, p <= start
    if p < start:
        p += n
    while len(out) < count:
        if isprime(p):
            out.append(p)
        p += n
    return out


def mulmod_split(a, b, p):
    """(a*b) % p for int64 arrays with 0 <= a,b < 2^33 without overflow (16-bit split of b)."""
    b_hi = b >> 16
    b_lo = b & 0xFFFF
    t = (a * b_hi) % p
    t = (t << 16) % p
    return (t + a * b_lo) % p


def coset_matrix(g, p, n, xs, i0, count):
    """rows = cosets g^i * mu_n for i in [i0, i0+count): shape (count, n), values in [1,p)."""
    # b_i = g^i mod p as Python ints (exact), then split-multiply by xs.
    bs = np.empty(count, dtype=np.int64)
    b = pow(g, i0, p)
    for k in range(count):
        bs[k] = b
        b = (b * g) % p
    return mulmod_split(bs[:, None], xs[None, :], p)


def max_window_counts(rows, p, Ls):
    """rows: (C, n) int64 in [0,p). Returns for each L the tuple (max count, row, start-elt)."""
    C, n = rows.shape
    S = np.sort(rows, axis=1)
    S2 = np.concatenate([S, S + p], axis=1)  # (C, 2n): cyclic windows
    off = (np.arange(C, dtype=np.int64) * (3 * p))[:, None]
    flat = (S2 + off).ravel()
    base = (S + off)  # (C, n)
    row_idx = np.arange(C, dtype=np.int64)[:, None] * (2 * n)
    j_idx = np.arange(n, dtype=np.int64)[None, :]
    out = []
    for L in Ls:
        q = (base + L).ravel()
        idx = np.searchsorted(flat, q, side="left")
        cnt = idx.reshape(C, n) - row_idx - j_idx  # #{k: S[j] <= S2[k] < S[j]+L}
        k = int(np.argmax(cnt))
        r, j = divmod(k, n)
        out.append((int(cnt[r, j]), r, int(S[r, j])))
    return out


def l_grid(p, n):
    """log grid of window lengths from 1 to p, plus the dyadic ladder around p/n."""
    K = 24 if FAST else 36
    Ls = set()
    for k in range(K + 1):
        Ls.add(max(1, min(p, int(round(p ** (k / K))))))
    pn = p // n
    for j in range(-3, 12):
        v = int(pn * (2.0 ** j))
        if 1 <= v <= p:
            Ls.add(v)
    return sorted(Ls)


def run_cell(n, p, budget_cosets, rng):
    g = primitive_root(p)
    m = (p - 1) // n
    x = pow(g, m, p)
    xs = np.array([pow(x, j, p) for j in range(n)], dtype=np.int64)
    assert len(set(xs.tolist())) == n
    Ls = l_grid(p, n)
    exact = m <= budget_cosets
    if exact:
        idxs = None
        total = m
    else:
        total = budget_cosets
        idxs = np.sort(rng.choice(m, size=total, replace=False))
    chunk = 1 << 14 if n >= 256 else 1 << 16
    best = {L: (0, -1, -1) for L in Ls}
    done = 0
    while done < total:
        c = min(chunk, total - done)
        if exact:
            rows = coset_matrix(g, p, n, xs, done, c)
            cos_base = done
            sel = None
        else:
            sel = idxs[done:done + c]
            bs = np.array([pow(g, int(i), p) for i in sel], dtype=np.int64)
            rows = mulmod_split(bs[:, None], xs[None, :], p)
            cos_base = None
        res = max_window_counts(rows, p, Ls)
        for L, (cnt, r, start) in zip(Ls, res):
            if cnt > best[L][0]:
                ci = (cos_base + r) if exact else int(sel[r])
                best[L] = (cnt, ci, start)
        done += c
    # random baseline with the same number of samples (capped for time)
    rtotal = min(total, 1 << 17 if not FAST else 1 << 15)
    rbest = {L: 0 for L in Ls}
    done = 0
    while done < rtotal:
        c = min(chunk, rtotal - done)
        rows = rng.integers(0, p, size=(c, n), dtype=np.int64)
        res = max_window_counts(rows, p, Ls)
        for L, (cnt, _, _) in zip(Ls, res):
            rbest[L] = max(rbest[L], cnt)
        done += c
    return m, exact, total, rtotal, Ls, best, rbest


def main():
    t0 = time.time()
    rng = np.random.default_rng(SEED)
    plan = [
        (8, 3, 1 << 20),
        (16, 3, 1 << 20),
        (32, 3, 1 << 20),
        (64, 2 if FAST else 3, 1 << 20),
        (128, 1 if FAST else 2, 1 << 15 if FAST else 1 << 17),
        (256, 1, 1 << 14 if FAST else 1 << 15),
    ]
    worst = []
    ok = True
    for n, nprimes, budget in plan:
        ps = primes_congruent_near(n, nprimes, n ** 4)
        for p in ps:
            tc = time.time()
            m, exact, total, rtotal, Ls, best, rbest = run_cell(n, p, budget, rng)
            norm = math.sqrt(n * math.log(p / n))
            print(f"\n=== n={n} p={p} (~n^{math.log(p)/math.log(n):.3f}) m={m} "
                  f"cosets={'EXACT all ' + str(m) if exact else 'SAMPLED ' + str(total)} "
                  f"random-baseline samples={rtotal} norm=sqrt(n ln(p/n))={norm:.3f}")
            print(f"{'L':>12} {'log_p L':>8} {'nL/p':>10} {'max':>5} {'excess':>8} {'R':>7} "
                  f"{'rand':>5} {'randR':>7} {'coset':>8} {'start':>10}")
            cell_worst = (-1e9, None)
            for L in Ls:
                cnt, ci, start = best[L]
                main = n * L / p
                exc = cnt - main
                R = exc / norm
                rR = (rbest[L] - main) / norm
                print(f"{L:>12} {math.log(L)/math.log(p):>8.3f} {main:>10.3f} {cnt:>5} "
                      f"{exc:>8.2f} {R:>7.3f} {rbest[L]:>5} {rR:>7.3f} {ci:>8} {start:>10}")
                if R > cell_worst[0]:
                    cell_worst = (R, L)
                if R > R_MAX:
                    ok = False
            R, L = cell_worst
            worst.append((n, p, exact, R, L, math.log(L) / math.log(p), L / (p / n)))
            print(f"--- cell worst R={R:.3f} at L={L} (log_p L={math.log(L)/math.log(p):.3f}, "
                  f"L/(p/n)={L/(p/n):.3g})  [{time.time()-tc:.1f}s]")
    print("\n=== SUMMARY (worst CLT-normalized excess per cell) ===")
    for n, p, exact, R, L, lg, ratio in worst:
        print(f"n={n:>4} p={p:>12} {'exact' if exact else 'sampled':>7} worstR={R:.3f} "
              f"at L={L} log_p L={lg:.3f} L/(p/n)={ratio:.3g}")
    print(f"total time {time.time()-t0:.1f}s")
    print("PASS: all measured R(L) <= %.1f (calibration threshold; measurement only)" % R_MAX
          if ok else "FAIL: some R(L) > %.1f" % R_MAX)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
