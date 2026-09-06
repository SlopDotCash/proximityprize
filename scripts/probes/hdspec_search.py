#!/usr/bin/env python3
"""
hdspec_search.py — exact-integer discrete thresholds for SPECTRAL caps of the order-d
hidden-derivative interpolant, and 2D local search over them.

A spectral cap is a set Omega of integer pairs (S, J); the monomial cap is
    cap(Omega) = { bs in N^d : (sum_j bs_j, sum_j j*bs_j) in Omega }.
Every functional of the counting rank bound depends on bs only through (S, J)
(W = w*S - J exactly), so the evaluation needs only the multiplicity
    N_d(S, J) = #{ bs in N^d : sum bs = S, sum j*bs = J }        (unbounded knapsack DP)
and runs in O(|Omega| + grid) per candidate at any derivative order d:

  * cols(g1, g2) = sum over (S,J) in Omega with S <= g1 - 0 (b0 = g1 - S >= 0),
      a = g2 + J in [0, m), weight a + w*b0 + (w*S - J) <= m*A - 1, of N_d(S, J)
    — accumulated as two rectangles per Omega-cell in (g1, g2) via a difference array;
  * rows(g1, g2) = #{(e, nE) in N^{d+1} : sum e + nE = g1,
      0 <= g2 + sum j*e_j + (d+1)*nE < m}  (cap-independent DP, prefix sums);
  * rank_bound = sum over blocks min(rows, cols)  — SOUND upper bound on the exact
    per-node constraint rank (block-diagonal invariants, rank <= #rows, #cols);
  * dim = sum over (S,J) in Omega of N_d(S,J) * sum_{b0} (D - w*b0 - (w*S - J)).

dim > n * rank_bound certifies a nonzero interpolant at agreement A (the Lean theorem
`exists_interpolant_d` consumes exactly this rank sum).  The search space is genuinely
2-dimensional at every d — the curse of dimension is gone.

Validated against hd_general_rank.node_rank / hd_fast_bound.rank_bound on box caps
converted to spectral form (box caps are unions of (S,J) cells with the box multiplicity,
NOT N_d, so the cross-check uses full wedges Omega = {(S,J): J <= dS, S <= smax} whose
cap(Omega) is the simplex {sum bs <= smax}).

Usage:
  python3 hdspec_search.py selftest
  python3 hdspec_search.py scan --rate 2 --d 6 --m 64
  python3 hdspec_search.py trend --rate 2 --d 6 --ms 32,48,64,96,128
"""
import argparse
import math
import os
import sys
from functools import lru_cache

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


@lru_cache(maxsize=None)
def multiplicity_table(d, smax, jmax):
    """N[S, J] = #{bs in N^d : sum = S, sum j*bs = J}, S <= smax, J <= jmax (int64;
    values are exact until they exceed 2^63 — callers should keep smax*d moderate)."""
    N = np.zeros((smax + 1, jmax + 1), dtype=np.object_)
    N[0, 0] = 1
    for j in range(1, d + 1):
        for s in range(1, smax + 1):
            N[s, j:] = N[s, j:] + N[s - 1, : jmax + 1 - j]
    return N


@lru_cache(maxsize=None)
def rows_table(d, m, g1max, jmax):
    """rows(g1, g2) for g2 in [-jmax, m): #{(e, nE): sum = g1,
    0 <= g2 + sum j e_j + (d+1) nE <= m-1}.  Returned as an integer-valued float array
    (row counts can be huge; only min(rows, cols) enters, so float64 is fine)."""
    sigmax = m - 1 + jmax
    T = np.zeros((g1max + 1, sigmax + 1), dtype=np.float64)
    T[0, 0] = 1.0
    for j in list(range(1, d + 1)) + [d + 1]:
        for g in range(1, g1max + 1):
            if j <= sigmax:
                T[g, j:] += T[g - 1, : sigmax + 1 - j]
    P = np.cumsum(T, axis=1)
    n2 = m + jmax
    R = np.zeros((g1max + 1, n2), dtype=np.float64)
    for idx in range(n2):
        g2 = idx - jmax
        hi = min(m - 1 - g2, sigmax)
        lo = -g2 - 1
        if hi < 0:
            continue
        col = P[:, hi].copy()
        if lo >= 0:
            col -= P[:, min(lo, sigmax)]
        R[:, idx] = col
    return R


class SpectralEvaluator:
    def __init__(self, d, n, k, m, smax=None, jmax=None):
        self.d, self.n, self.k, self.m = d, n, k, m
        self.w = k - 1
        assert m <= self.w
        self.smax = smax or 2 * m
        self.jmax = jmax or min(d, 24) * self.smax
        self.mult = multiplicity_table(d, self.smax, self.jmax)

    def threshold(self, omega, lo=None, hi=None):
        """omega: iterable of (S, J) integer pairs.  Least A with dim > n*rank_bound."""
        d, n, k, m, w = self.d, self.n, self.k, self.m, self.w
        cells = [(S, J, int(self.mult[S, J])) for (S, J) in omega
                 if S <= self.smax and J <= self.jmax and self.mult[S, J] > 0]
        if not cells:
            return None
        lo = lo or k
        hi = hi or n
        if not self.feasible(cells, hi):
            return None
        while lo < hi:
            mid = (lo + hi) // 2
            if self.feasible(cells, mid):
                hi = mid
            else:
                lo = mid + 1
        return lo

    def feasible(self, cells, A):
        d, n, m, w = self.d, self.n, self.m, self.w
        D = m * A
        jmax = max(J for (S, J, N) in cells)
        smax_c = max(S for (S, J, N) in cells)
        g1max = smax_c + (D - 1) // w + 1
        ROWS = rows_table(d, m, g1max, jmax)
        n2 = m + jmax
        diff = np.zeros((g1max + 2, n2 + 1), dtype=np.float64)
        dim = 0
        for (S, J, N) in cells:
            W = w * S - J
            top = D - 1 - W
            if top < 0:
                continue
            # dimension: sum_{b0 <= (D-W-1)//w} (D - W - w b0)
            R0 = D - W
            b0m = (R0 - 1) // w
            dim += N * ((b0m + 1) * R0 - w * (b0m * (b0m + 1)) // 2)
            q, r = divmod(top, w)
            ahi = min(m - 1, top)
            a1 = min(r, ahi)
            gl, gh = S, S + q
            c0, c1 = jmax + (0 - J), jmax + (a1 - J)
            diff[gl, c0] += N
            diff[gh + 1, c0] -= N
            diff[gl, c1 + 1] -= N
            diff[gh + 1, c1 + 1] += N
            if a1 < ahi and q >= 1:
                c2, c3 = jmax + (a1 + 1 - J), jmax + (ahi - J)
                diff[gl, c2] += N
                diff[gh, c2] -= N
                diff[gl, c3 + 1] -= N
                diff[gh, c3 + 1] += N
        cols = np.cumsum(np.cumsum(diff, axis=0), axis=1)[: g1max + 1, : n2]
        rb = np.minimum(ROWS, cols).sum()
        return dim > n * rb


def wedge(d, smax, srange=None):
    """Full wedge {(S,J): 0 <= S <= smax, S <= J <= d*S} = the simplex cap sum bs <= smax."""
    out = []
    for S in range(smax + 1):
        for J in range(S, d * S + 1):
            out.append((S, J))
    return out


def selftest():
    from hd_general_rank import node_rank, dim_space
    from hd_fast_bound import rank_bound
    n, k = 1 << 18, 1 << 17
    w = k - 1
    fails = 0
    print("== spectral wedge == simplex cap: dim and counting threshold cross-check")
    for (d, m, smax) in [(2, 8, 3), (3, 12, 4), (2, 12, 5)]:
        ev = SpectralEvaluator(d, n, k, m, smax=smax, jmax=d * smax)
        om = wedge(d, smax)
        simplex = ((smax,) * d, lambda bs, s=smax: sum(bs) <= s)
        A1 = ev.threshold(om, lo=170000)
        # reference: bisection on hd_fast_bound with the simplex cap
        def ok(A):
            return dim_space(d, w, m * A, simplex) > n * rank_bound(
                d, m, w, m * A, simplex, exact_rows=False)
        lo, hi = 170000, n
        if not ok(hi):
            ref = None
        else:
            while lo < hi:
                mid = (lo + hi) // 2
                if ok(mid):
                    hi = mid
                else:
                    lo = mid + 1
            ref = lo
        exact_thr = None
        okx = (A1 == ref)
        fails += 0 if okx else 1
        print(f"  d={d} m={m} simplex smax={smax}: spectral={A1} ref={ref} "
              f"{'OK' if okx else 'MISMATCH'}")
    print("SELFTEST", "PASS" if fails == 0 else "FAIL")
    return fails


def neighbors(omega_set, d, smax, jmax):
    adds, removes = set(), []
    for (S, J) in omega_set:
        removes.append((S, J))
        for (dS, dJ) in ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, d)):
            c = (S + dS, J + dJ)
            if c not in omega_set and 0 <= c[0] <= smax and c[0] <= c[1] <= d * c[0] \
                    and c[1] <= jmax:
                adds.add(c)
    return list(adds), removes


def local_search(ev, omega0, rounds=400, seed=0, verbose=True):
    import random
    rng = random.Random(seed)
    omega = set(omega0)
    best = ev.threshold(omega)
    if best is None:
        return omega, None
    for it in range(rounds):
        adds, removes = neighbors(omega, ev.d, ev.smax, ev.jmax)
        moves = [("+", c) for c in adds] + [("-", c) for c in removes]
        rng.shuffle(moves)
        improved = False
        for kind, c in moves:
            cand = set(omega)
            (cand.add if kind == "+" else cand.discard)(c)
            if not cand:
                continue
            cells = [(S, J, int(ev.mult[S, J])) for (S, J) in cand if ev.mult[S, J] > 0]
            if not cells:
                continue
            if ev.feasible(cells, best - 1):
                A2 = ev.threshold(cand, hi=best - 1)
                if A2 is not None and A2 < best:
                    omega, best = cand, A2
                    improved = True
                    if verbose:
                        print(f"    it{it} {kind}{c} -> A={best} |omega|={len(omega)}",
                              flush=True)
                    break
        if not improved:
            break
    return omega, best


def scan(rate_denom, d, m, nexp=18, rounds=400, seed=0):
    n = 1 << nexp
    k = n // rate_denom
    ev = SpectralEvaluator(d, n, k, m)
    AJ = math.ceil(math.sqrt(n * (k - 1)))
    print(f"SPECTRAL d={d} m={m} rate=1/{rate_denom} n=2^{nexp} Johnson A={AJ}",
          flush=True)
    results = []
    starts = []
    # S-cap wedges at several sizes (the d=1-style caps)
    for f in (0.20, 0.31, 0.45):
        s0 = max(1, round(f * m))
        starts.append((f"wedge{s0}", wedge(d, s0)))
    for name, om0 in starts:
        A0 = ev.threshold(om0)
        if A0 is None:
            print(f"  start={name}: infeasible", flush=True)
            continue
        om, A = local_search(ev, om0, rounds=rounds, seed=seed, verbose=False)
        r = A / math.sqrt(n * (k - 1))
        print(f"  start={name:<10} A0={A0} -> A={A} ratio={r:.6f} "
              f"delta={1 - A / n:.5f} |omega|={len(om)}", flush=True)
        results.append((A, om, name))
    results.sort(key=lambda t: t[0])
    A, om, name = results[0]
    Ss = sorted(set(S for (S, J) in om))
    print(f"  BEST A={A} ({name}); S-range {Ss[0]}..{Ss[-1]}; "
          f"J/S envelope: " + " ".join(
              f"{S}:{min(J for (s2, J) in om if s2 == S)}-"
              f"{max(J for (s2, J) in om if s2 == S)}"
              for S in Ss[:8]), flush=True)
    return A, om


def trunc_wedge(d, smax, jcap):
    """Omega(Smax, Jcap) = {(S,J): S <= Smax, S <= J <= min(d*S, Jcap)}."""
    out = []
    for S in range(smax + 1):
        for J in range(S, min(d * S, jcap) + 1):
            out.append((S, J))
    return out


def paramscan(rate_denom, d, m, nexp=18, refine=True, verbose=True):
    """Deterministic scan over the truncated-wedge family, then optional local search."""
    n = 1 << nexp
    k = n // rate_denom
    ev = SpectralEvaluator(d, n, k, m)
    s = math.sqrt(n * (k - 1))
    best = (None, None, None)
    smax_grid = sorted(set(max(1, round(m * f)) for f in
                           (0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.65, 0.8)))
    jcap_grid = sorted(set(max(1, round(m * f)) for f in
                           (0.25, 0.4, 0.55, 0.7, 0.9, 1.2, 1.6, 2.2, 3.0)))
    for smax in smax_grid:
        for jcap in jcap_grid:
            om = trunc_wedge(d, smax, jcap)
            A = ev.threshold(om, hi=(best[0] or n))
            if A is not None and (best[0] is None or A < best[0]):
                best = (A, smax, jcap)
                if verbose:
                    print(f"    smax={smax} jcap={jcap}: A={A} ({A / s:.5f})", flush=True)
    A, smax, jcap = best
    om = set(trunc_wedge(d, smax, jcap))
    if refine and A is not None:
        om, A2 = local_search(ev, om, rounds=200, verbose=False)
        if A2 is not None and A2 < A:
            A = A2
    print(f"  PARAM d={d} m={m}: A={A} ratio={A / s:.6f} delta={1 - A / n:.5f} "
          f"(smax={smax} jcap={jcap}, refined |omega|={len(om)})", flush=True)
    return A, om


def trend(rate_denom, d, ms, nexp=18, rounds=300):
    n = 1 << nexp
    k = n // rate_denom
    s = math.sqrt(n * (k - 1))
    out = []
    for m in ms:
        A, om = scan(rate_denom, d, m, nexp=nexp, rounds=rounds)
        out.append((m, A))
        print(f"  TREND d={d} m={m}: A={A} ratio={A / s:.6f}", flush=True)
    print("== trend " + "  ".join(f"m{m}:{A}({A / s:.5f})" for m, A in out), flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["selftest", "scan", "trend", "paramtrend"])
    ap.add_argument("--rate", type=int, default=2)
    ap.add_argument("--d", type=int, default=6)
    ap.add_argument("--m", type=int, default=64)
    ap.add_argument("--ms", type=str, default="32,48,64,96")
    ap.add_argument("--nexp", type=int, default=18)
    ap.add_argument("--rounds", type=int, default=400)
    args = ap.parse_args()
    if args.cmd == "selftest":
        sys.exit(1 if selftest() else 0)
    elif args.cmd == "scan":
        scan(args.rate, args.d, args.m, nexp=args.nexp, rounds=args.rounds)
    elif args.cmd == "paramtrend":
        n = 1 << args.nexp
        k = n // args.rate
        s = math.sqrt(n * (k - 1))
        out = []
        for m in [int(x) for x in args.ms.split(",")]:
            A, _ = paramscan(args.rate, args.d, m, nexp=args.nexp)
            out.append((m, A))
        print("== paramtrend d=%d " % args.d + "  ".join(
            f"m{m}:{A}({A / s:.5f})" for m, A in out), flush=True)
    else:
        trend(args.rate, args.d, [int(x) for x in args.ms.split(",")],
              nexp=args.nexp, rounds=args.rounds)
