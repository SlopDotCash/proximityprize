#!/usr/bin/env python3
"""
hdinf_cap_search.py — downset cap-shape search for the order-d hidden-derivative
interpolation threshold (LD setting), and the d -> infinity trend at the prize rates.

Novelty over hd_fast_bound.py: the counting rank bound is evaluated in O(|cap| + grid)
per candidate instead of per-column enumeration, by

  * a cap-INDEPENDENT row-count table  rows(g1, g2) = #{(e in N^d, nE) : sum e + nE = g1,
    0 <= g2 + sum_j j*e_j + (d+1)*nE < m}  computed once per (d, m) by an unbounded-knapsack
    DP with prefix sums over the weighted degree; and
  * per-bs COLUMN rectangles: for a fixed derivative tuple bs, the columns (a, b0) of the
    interpolant occupy at most two axis-aligned rectangles in block coordinates
    (g1, g2) = (b0 + S(bs), a - J(bs)) (b0max = (D-1-a-W(bs))//w takes at most two values as
    a ranges over [0, m) when m <= w), accumulated by a 2D difference array in O(1) each.

rank_bound = sum over blocks of min(rows, cols) is a SOUND upper bound on the exact per-node
rank (blocks are invariant, rank <= min(#rows, #cols)); dim > n * rank_bound certifies the
interpolant exists.  Cross-checked against hd_fast_bound.rank_bound (exact_rows=False) and
against hd_general_rank.node_rank on the selftest grid.

The cap is searched over arbitrary DOWNSETS of N^d (monotone sets: bs in cap and bs' <= bs
pointwise implies bs' in cap), the true design space of the method; boxes, simplices and
TR26-164 omega-caps are the warm starts.  Moves add a point whose predecessors are all in the
cap or remove a point with no successor in the cap.

Usage:
  python3 hdinf_cap_search.py selftest
  python3 hdinf_cap_search.py scan --rate 2 --d 3 --m 64            # local search at one config
  python3 hdinf_cap_search.py trend --rate 2                        # d/m sweep with search
"""
import argparse
import math
import random
import sys
import os
from itertools import product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


# ---------------------------------------------------------------- row tables

def row_table(d, m, g1max, jmax):
    """N[g1, sigma] = #{(e_1..e_d, nE) >= 0 : sum = g1, sum_j j*e_j + (d+1)*nE = sigma}
    for g1 <= g1max, sigma <= sigmax = m - 1 + jmax; then prefix sums over sigma.
    Returns P with P[g1, t] = sum_{sigma <= t} N[g1, sigma]."""
    sigmax = m - 1 + jmax
    N = np.zeros((g1max + 1, sigmax + 1), dtype=np.float64)
    N[0, 0] = 1.0
    for j in list(range(1, d + 1)) + [d + 1]:
        # unbounded item with (count 1, weight j): forward in-place
        for g in range(1, g1max + 1):
            N[g, j:] += N[g - 1, : sigmax + 1 - j]
    return np.cumsum(N, axis=1)


def rows_grid(P, m, g1max, g2min):
    """rows[g1, g2 - g2min] for g2 in [g2min, m-1]:  sum_{sigma <= m-1-g2} N[g1, sigma]
    (sigma >= max(0,-g2) is automatic: N[g1, sigma] = 0 unless sigma >= g1 >= 0, and
    columns with g2 < 0 need sigma >= -g2 which holds since row i = g2 + sigma >= 0 is
    exactly the prefix cut below)."""
    sigmax = P.shape[1] - 1
    n2 = m - g2min
    out = np.zeros((g1max + 1, n2), dtype=np.float64)
    for idx, g2 in enumerate(range(g2min, m)):
        hi = min(m - 1 - g2, sigmax)
        lo = -g2 - 1  # exclude sigma <= -g2-1 (row i = g2 + sigma < 0)
        if hi < 0:
            continue
        col = P[:, hi].copy()
        if lo >= 0:
            col -= P[:, min(lo, sigmax)]
        out[:, idx] = col
    return out


# ---------------------------------------------------------------- cap objects

def cap_stats(cap, d, w):
    """Per-bs invariants: S = sum bs, J = sum (j+1) bs_j, W = sum (w-1-j) bs_j."""
    out = []
    for bs in cap:
        S = sum(bs)
        J = sum((j + 1) * bs[j] for j in range(d))
        W = sum((w - 1 - j) * bs[j] for j in range(d))
        out.append((S, J, W))
    return out


def dim_cap(stats, w, D):
    tot = 0
    for (S, J, W) in stats:
        R = D - W
        if R <= 0:
            continue
        b0m = (R - 1) // w
        tot += (b0m + 1) * R - w * (b0m * (b0m + 1)) // 2
    return tot


def rank_bound_fast(stats, d, m, w, D, ROWS, g1max, g2min):
    """Counting rank bound via rectangle accumulation.  Requires m <= w."""
    n2 = m - g2min
    diff = np.zeros((g1max + 2, n2 + 1), dtype=np.float64)

    def add_rect(gl, gh, cl, ch):
        # +1 on g1 in [gl, gh], g2-index in [cl, ch]
        diff[gl, cl] += 1.0
        diff[gh + 1, cl] -= 1.0
        diff[gl, ch + 1] -= 1.0
        diff[gh + 1, ch + 1] += 1.0

    for (S, J, W) in stats:
        top = D - 1 - W
        if top < 0:
            continue
        q, r = divmod(top, w)
        # a in [0, min(m-1, top)]: b0max = q for a <= r, q-1 for a > r
        ahi = min(m - 1, top)
        a1 = min(r, ahi)
        # range 1: a in [0, a1], b0 in [0, q]
        add_rect(S, S + q, -g2min + (0 - J), -g2min + (a1 - J))
        # range 2: a in (a1, ahi], b0 in [0, q-1]
        if a1 < ahi and q >= 1:
            add_rect(S, S + q - 1, -g2min + (a1 + 1 - J), -g2min + (ahi - J))
    cols = np.cumsum(np.cumsum(diff, axis=0), axis=1)[: g1max + 1, : n2]
    return float(np.minimum(ROWS, cols).sum())


class Evaluator:
    """Threshold evaluator for downset caps at fixed (d, n, k, m)."""

    def __init__(self, d, n, k, m, jmax_hint=None):
        self.d, self.n, self.k, self.m = d, n, k, m
        self.w = k - 1
        assert m <= self.w, "rectangle argument needs m <= w"
        self.jmax = jmax_hint or (d + 1) * 4 * m  # refreshed per cap below
        self._tables = {}

    def _get_tables(self, g1max, g2min):
        key = (g1max, g2min)
        if key not in self._tables:
            P = row_table(self.d, self.m, g1max, -g2min)
            self._tables[key] = rows_grid(P, self.m, g1max, g2min)
        return self._tables[key]

    def threshold(self, cap, lo=None, hi=None):
        """Least A with dim > n * rank_bound, or None."""
        d, n, k, m, w = self.d, self.n, self.k, self.m, self.w
        stats = cap_stats(cap, d, w)
        jmax = max((J for (_, J, _) in stats), default=0)
        lo = lo or k
        hi = hi or n
        # g1 range: b0max at largest D (= m*hi) is (m*hi-1)//w; add S
        smax = max((S for (S, _, _) in stats), default=0)

        def ok(A):
            D = m * A
            g1max = smax + (D - 1) // w + 1
            g2min = -jmax
            ROWS = self._get_tables(g1max, g2min)
            rb = rank_bound_fast(stats, d, m, w, D, ROWS, g1max, g2min)
            dq = dim_cap(stats, w, D)
            return dq > n * rb

        if not ok(hi):
            return None
        while lo < hi:
            mid = (lo + hi) // 2
            if ok(mid):
                hi = mid
            else:
                lo = mid + 1
        return lo

    def margin(self, cap, A):
        d, n, m, w = self.d, self.n, self.m, self.w
        stats = cap_stats(cap, d, w)
        jmax = max((J for (_, J, _) in stats), default=0)
        smax = max((S for (S, _, _) in stats), default=0)
        D = m * A
        g1max = smax + (D - 1) // w + 1
        ROWS = self._get_tables(g1max, -jmax)
        rb = rank_bound_fast(stats, d, m, w, D, ROWS, g1max, -jmax)
        return dim_cap(stats, w, D) - n * rb


# ---------------------------------------------------------------- downsets

def box_cap(caps):
    return frozenset(product(*[range(c + 1) for c in caps]))


def omega_cap_set(d, s1, Wm):
    """b_1 <= s1, sum_{j>=2} (j-1) b_j <= Wm  (TR26-164 shape)."""
    pts = []
    box = [s1] + [Wm // (j - 1) for j in range(2, d + 1)]
    for bs in product(*[range(b + 1) for b in box]):
        if sum((j - 1) * bs[j - 1] for j in range(2, d + 1)) <= Wm:
            pts.append(bs)
    return frozenset(pts)


def frontier_moves(cap, d, degmax):
    """(adds, removes) preserving the downset property."""
    capset = cap
    adds, removes = [], []
    for bs in capset:
        # removable if no successor in cap
        if all(tuple(bs[i] + (1 if i == j else 0) for i in range(d)) not in capset
               for j in range(d)):
            if sum(bs) > 0:
                removes.append(bs)
        for j in range(d):
            up = tuple(bs[i] + (1 if i == j else 0) for i in range(d))
            if up in capset or up[j] > degmax:
                continue
            if all((tuple(up[i] - (1 if i == jj else 0) for i in range(d)) in capset)
                   for jj in range(d) if up[jj] > 0):
                adds.append(up)
    return list(set(adds)), removes


def local_search(ev, cap, degmax, rounds=200, seed=0, verbose=True):
    rng = random.Random(seed)
    best = ev.threshold(cap)
    if verbose:
        print(f"    start |cap|={len(cap)} A={best}", flush=True)
    stall = 0
    for it in range(rounds):
        adds, removes = frontier_moves(cap, ev.d, degmax)
        moves = [("+", p) for p in adds] + [("-", p) for p in removes]
        rng.shuffle(moves)
        improved = False
        for kind, p in moves:
            cand = set(cap)
            if kind == "+":
                cand.add(p)
            else:
                cand.discard(p)
            if not cand:
                continue
            cand = frozenset(cand)
            # accept if threshold strictly drops (margin > 0 at best-1)
            if ev.margin(cand, best - 1) > 0:
                A2 = ev.threshold(cand, hi=best - 1)
                if A2 is not None and A2 < best:
                    cap, best = cand, A2
                    improved = True
                    if verbose:
                        print(f"    it{it} {kind}{p} -> A={best} |cap|={len(cap)}", flush=True)
                    break
        if not improved:
            # allow sideways moves (equal A) a few times to escape plateaus
            stall += 1
            side = None
            for kind, p in moves:
                cand = set(cap)
                (cand.add if kind == "+" else cand.discard)(p)
                if not cand:
                    continue
                cand = frozenset(cand)
                if ev.margin(cand, best) > 0 and ev.threshold(cand, hi=best) == best:
                    side = cand
                    break
            if side is not None and stall <= 8:
                cap = side
            else:
                break
    return cap, best


# ---------------------------------------------------------------- validation

def selftest():
    from hd_fast_bound import rank_bound as rb_ref, omega_cap as om_ref
    from hd_general_rank import node_rank, dim_space
    n, k = 1 << 18, 1 << 17
    w = k - 1
    fails = 0
    print("== fast rectangles vs hd_fast_bound.rank_bound(exact_rows=False) and exact rank")
    for (d, m, s) in [(1, 8, (2,)), (1, 12, (3,)), (2, 8, (2, 1)), (2, 12, (3, 2)),
                      (3, 12, ((3, 2, 1), None))]:
        if isinstance(s, tuple) and len(s) == 2 and s[1] is None:
            cap = box_cap(s[0])
            sref = s[0]
        else:
            cap = box_cap(s)
            sref = s
        A = 184000
        D = m * A
        stats = cap_stats(cap, d, w)
        jmax = max(J for (_, J, _) in stats)
        smax = max(S for (S, _, _) in stats)
        g1max = smax + (D - 1) // w + 1
        P = row_table(d, m, g1max, jmax)
        ROWS = rows_grid(P, m, g1max, -jmax)
        mine = rank_bound_fast(stats, d, m, w, D, ROWS, g1max, -jmax)
        ref = rb_ref(d, m, w, D, sref, exact_rows=False)
        exact = node_rank(d, m, w, D, sref)
        dq_mine = dim_cap(stats, w, D)
        dq_ref = dim_space(d, w, D, sref)
        ok = (int(mine) == ref) and (mine >= exact) and (dq_mine == dq_ref)
        fails += 0 if ok else 1
        print(f"  d={d} m={m} s={sref}: fast={int(mine)} ref={ref} exact={exact} "
              f"dim {dq_mine}=={dq_ref} {'OK' if ok else 'MISMATCH'}")
    print("== thresholds: Evaluator vs hd_fast_bound.min_agreement_bound")
    from hd_fast_bound import min_agreement_bound
    for (d, m, s) in [(1, 12, (3,)), (2, 12, (3, 2))]:
        ev = Evaluator(d, n, k, m)
        A1 = ev.threshold(box_cap(s), lo=170000)
        A2 = min_agreement_bound(d, n, k, m, s, lo=170000)
        # exact_rows=True in the reference is tighter (smaller row sets), so A2 <= A1 need not
        # hold; compare against the same exact_rows=False accounting via direct bisection.
        def ok_ref(A):
            from hd_fast_bound import rank_bound
            return dim_space(d, w, m * A, s) > n * rank_bound(d, m, w, m * A, s,
                                                              exact_rows=False)
        lo, hi = 170000, n
        while lo < hi:
            mid = (lo + hi) // 2
            if ok_ref(mid):
                hi = mid
            else:
                lo = mid + 1
        ok = (A1 == lo)
        fails += 0 if ok else 1
        print(f"  d={d} m={m} s={s}: A_fast={A1} A_ref(exact_rows=False)={lo} "
              f"(exact_rows=True ref {A2}) {'OK' if ok else 'MISMATCH'}")
    print("SELFTEST", "PASS" if fails == 0 else "FAIL")
    return fails


# ---------------------------------------------------------------- drivers

def johnson(n, k):
    return math.ceil(math.sqrt(n * (k - 1)))


RESULTS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "hdinf_results")


def _cap_path(rate_denom, d, m, nexp):
    return os.path.join(RESULTS_DIR, f"cap_r{rate_denom}_d{d}_m{m}_n{nexp}.json")


def save_cap(rate_denom, d, m, nexp, A, cap):
    import json
    os.makedirs(RESULTS_DIR, exist_ok=True)
    with open(_cap_path(rate_denom, d, m, nexp), "w") as fh:
        json.dump({"A": A, "cap": sorted(list(map(list, cap)))}, fh)


def load_cap(rate_denom, d, m, nexp):
    import json
    p = _cap_path(rate_denom, d, m, nexp)
    if not os.path.exists(p):
        return None, None
    with open(p) as fh:
        obj = json.load(fh)
    return obj["A"], frozenset(map(tuple, obj["cap"]))


def scan(rate_denom, d, m, nexp=18, rounds=200, seed=0, seeds=2):
    n = 1 << nexp
    k = n // rate_denom
    ev = Evaluator(d, n, k, m)
    AJ = johnson(n, k)
    print(f"d={d} m={m} rate=1/{rate_denom} n=2^{nexp}  Johnson A={AJ}", flush=True)
    results = []
    # warm starts
    starts = []
    s1 = max(1, round(0.31 * m)) if rate_denom == 2 else max(1, round(0.55 * m))
    starts.append(("box-quarter", box_cap((max(1, m // 4),) * min(d, 1) +
                                          tuple(max(1, m // 8) for _ in range(d - 1)))))
    if d >= 2:
        for Wm in {max(1, m // 8), max(1, m // 4)}:
            starts.append((f"omega{Wm}", omega_cap_set(d, s1, Wm)))
        # embed the best (d-1)-cap with b_d = 0
        _, prev = load_cap(rate_denom, d - 1, m, nexp)
        if prev is not None:
            starts.append(("embed-prev-d", frozenset(bs + (0,) for bs in prev)))
    # scale the best cap at m//2 by 2 (profile continuation)
    _, half = load_cap(rate_denom, d, m // 2, nexp)
    if half is not None:
        scaled = set()
        for bs in half:
            for delta in product(*[(0, 1)] * d):
                scaled.add(tuple(2 * bs[j] + delta[j] for j in range(d)))
        # close downward
        scaled_ds = set()
        for bs in scaled:
            scaled_ds.update(product(*[range(b + 1) for b in bs]))
        starts.append(("scale-half-m", frozenset(scaled_ds)))
    for name, cap0 in starts:
        A0 = ev.threshold(cap0)
        if A0 is None:
            print(f"  start={name:<12} |cap0|={len(cap0):>6} A0=None (skip)", flush=True)
            continue
        for sd in range(seeds):
            cap, A = local_search(ev, cap0, degmax=2 * m, rounds=rounds,
                                  seed=seed + sd, verbose=False)
            r = A / math.sqrt(n * (k - 1))
            print(f"  start={name:<12} seed={seed + sd} |cap0|={len(cap0):>6} A0={A0}  "
                  f"->  A={A} ratio={r:.6f} delta={1 - A / n:.5f} |cap|={len(cap)}",
                  flush=True)
            results.append((A, cap, name))
    results.sort(key=lambda t: t[0])
    A, cap, name = results[0]
    prof = profile(cap, d)
    prevA, prevcap = load_cap(rate_denom, d, m, nexp)
    if prevA is None or A < prevA:
        save_cap(rate_denom, d, m, nexp, A, cap)
    else:
        A, cap = prevA, prevcap
    print(f"  BEST A={A} from {name}; cap per-axis max: {prof}", flush=True)
    return A, cap


def profile(cap, d):
    mx = [max((bs[j] for bs in cap), default=0) for j in range(d)]
    return mx


def trend(rate_denom, nexp=18, rounds=150, ms=(16, 32, 48, 64, 96), ds=(1, 2, 3, 4, 5)):
    print(f"== d/m trend at rate 1/{rate_denom}, n=2^{nexp} (counting bound, downset search)")
    table = {}
    for m in ms:
        for d in ds:
            try:
                A, _ = scan(rate_denom, d, m, nexp=nexp, rounds=rounds)
                table[(m, d)] = A
            except AssertionError:
                table[(m, d)] = None
        print("  SUMMARY " + f"m={m:>3}  " +
              "  ".join(f"d{d}:{table[(m, d)]}" for d in ds), flush=True)
    print("== final table (A; ratio to sqrt(n(k-1)))")
    n = 1 << nexp
    k = n // rate_denom
    s = math.sqrt(n * (k - 1))
    for m in ms:
        print("  " + f"m={m:>3}  " + "  ".join(
            f"d{d}:{table[(m, d)]}({table[(m, d)] / s:.5f})" if table[(m, d)] else f"d{d}:-"
            for d in ds), flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["selftest", "scan", "trend"])
    ap.add_argument("--rate", type=int, default=2)
    ap.add_argument("--d", type=int, default=3)
    ap.add_argument("--m", type=int, default=64)
    ap.add_argument("--nexp", type=int, default=18)
    ap.add_argument("--rounds", type=int, default=200)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    if args.cmd == "selftest":
        sys.exit(1 if selftest() else 0)
    elif args.cmd == "scan":
        scan(args.rate, args.d, args.m, nexp=args.nexp, rounds=args.rounds, seed=args.seed)
    else:
        trend(args.rate, nexp=args.nexp)
