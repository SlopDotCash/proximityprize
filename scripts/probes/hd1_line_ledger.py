#!/usr/bin/env python3
"""
hd1_line_ledger.py — port of the conservative seed-count ledger of better.codes PR #122
(nasqret, `ContactAlignmentParameters.lean`, commit b3fac81a) to general parameters, plus the
exact d=1 line interpolation gate, and a search for a large certified radius for a given
(n, w, field size, epsilon*) under that ledger.  The joint predicate is NOT monotone in the
agreement a (see `least_passing`), so the radius is proved largest (least a) only for ranges
small enough to scan exhaustively; at prize scale the search is bisection and each reported
radius is certified but not proved optimal.

Ledger (verbatim structure of the Lean definitions, parametrized):
  yCap   = floor((m*a - 1)/w)                     (Y-degree cap forced by weighted degree)
  gap    = a - w,  e = n - a,  jcap = (2s-1)*L     (algebraic/singular cap)
  E      = (1 + 2w*yCap, w*(2s-1), 2wL + 1)       (agreement vector)
  tail(h)= (1 + 2h*yCap, h*(2s-1), 2hL)            firstTail = tail(w+1), lastTail = tail(m*a)
  mixed(a,b,c) = coefficient of UVW in (a.U)(b.U)(c.U)  (sum over 6 permutations)
  whole(v) = n(n-w) mixed(v,E,E) + (e+1)(n-w) gap mixed(v,E,unitZ)
  cut(v)   = gap^2 mixed(v,first,last) + n gap mixed(v,first,E) + (e+1) gap^2 mixed(v,first,unitZ)
  regular  = yCap*max(cut(Y),whole(Y)) + s*max(cut(R),whole(R)) + L*max(cut(Z),whole(Z))
  singular = gap*(j + 2j^2 + j(1 + 2(w+1)(j-1)) + (e+1)j) + n*j(1 + 2w(j-1)),  j = jcap
  total    = regular + gap*singular ;   seeds <= total / gap^2  (strict: total < B*gap^2)

The Lean development proves the geometric inputs for the FIXED profile; whether every
geometric theorem there is parametric in (n, w, a, m, s, L) must be audited separately
(see the KB note).  This file only evaluates the arithmetic ledger at other parameters.

Interpolation gate (exact): dim Q > n * rank(Phi) with rank(Phi) the exact per-node rank
(hd1_interpolation_threshold.line_rank_blocks, computed over F_P with P = 2^31 - 1), which
coincides with nasqret's closed-form `localContactRank` (checked below at the PR profile:
49960; a mismatch fails the run).  Transporting a modular rank to another characteristic needs
its own argument.

Run: python3 scripts/probes/hd1_line_ledger.py
"""
import math
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hd1_interpolation_threshold import line_rank_blocks, line_dim  # noqa: E402


def mixed(a, b, c):
    return (a[0] * b[1] * c[2] + a[0] * b[2] * c[1] + a[1] * b[0] * c[2] + a[1] * b[2] * c[0]
            + a[2] * b[0] * c[1] + a[2] * b[1] * c[0])


UNIT_Y, UNIT_R, UNIT_Z = (1, 0, 0), (0, 1, 0), (0, 0, 1)


def ledger(n, w, a, m, s, L):
    """Return (total_numerator, gap, seeds_upper_bound_float)."""
    D = m * a
    yCap = (D - 1) // w
    gap = a - w
    e = n - a
    j = (2 * s - 1) * L
    E = (1 + 2 * w * yCap, w * (2 * s - 1), 2 * w * L + 1)
    tail = lambda h: (1 + 2 * h * yCap, h * (2 * s - 1), 2 * h * L)
    first, last = tail(w + 1), tail(D)

    def whole(v):
        return n * (n - w) * mixed(v, E, E) + (e + 1) * (n - w) * gap * mixed(v, E, UNIT_Z)

    def cut(v):
        return (gap ** 2 * mixed(v, first, last) + n * gap * mixed(v, first, E)
                + (e + 1) * gap ** 2 * mixed(v, first, UNIT_Z))
    regular = (yCap * max(cut(UNIT_Y), whole(UNIT_Y)) + s * max(cut(UNIT_R), whole(UNIT_R))
               + L * max(cut(UNIT_Z), whole(UNIT_Z)))
    singular = (gap * (j + 2 * j * j + j * (1 + 2 * (w + 1) * (j - 1)) + (e + 1) * j)
                + n * j * (1 + 2 * w * (j - 1)))
    total = regular + gap * singular
    return total, gap, total / gap ** 2


def local_contact_rank(m, s, L):
    """nasqret's closed form `localContactRank` (d=1 line setting, y1 != 0)."""
    def ce(r):
        return min(r + 1, m - r)
    tot = 0
    for r in range(m):
        t1 = (s + 1) * sum((L + 1 - f) for f in range(min(r, L) + 1))
        c = ce(r)
        t2 = 0
        if s + 1 - c > 0 and min(r, L) + 1 - c > 0:
            t2 = (s + 1 - c) * sum((L + 1 - c - f) for f in range(min(r, L) + 1 - c))
        tot += t1 - t2
    return tot


def interpolation_ok(n, w, a, m, s, L, exact=True):
    D = m * a
    dq = line_dim(D, w, s, L)
    if exact:
        r, _, _ = line_rank_blocks(D, w, s, L, m)
    else:
        r = local_contact_rank(m, s, L)
    return dq > n * r, dq, r


def certify(n, w, a, m, s, L, budget, exact=False):
    ok, dq, r = interpolation_ok(n, w, a, m, s, L, exact=exact)
    total, gap, seeds = ledger(n, w, a, m, s, L)
    return ok and (total < budget * gap * gap), dict(dimQ=dq, rank=r, seeds=seeds, gap=gap)


EXHAUSTIVE_LIMIT = 4096


def least_passing(ok, lo, hi, exhaustive_limit=EXHAUSTIVE_LIMIT):
    """Least a in [lo, hi] with ok(a), returned as (a, proved_least).

    The joint predicate (interpolation gate AND ledger budget) is NOT monotone in a: the seed
    estimate total/gap^2 can increase with a, because yCap and the tails grow with D = m*a.
    Audit L105 example, exact integers: (n,w,m,s,L,B) = (6,2,2,1,2,5711) passes at a = 5
    (51390 < 5711*9) but fails at a = 6 (119856 > 5711*16), so endpoint-skip + bisection
    wrongly reported no certified radius.

    Ranges of at most `exhaustive_limit` values are scanned exhaustively: (a, True) is then the
    least passing agreement and (None, True) proves that none exists in [lo, hi].  Larger ranges
    fall back to bisection, which keeps the invariant ok(hi) and so returns a CERTIFIED passing a,
    but flagged proved_least=False (a smaller passing a may exist); if the endpoint hi fails it
    returns (None, False), meaning "not found", not "none exists"."""
    if hi - lo + 1 <= exhaustive_limit:
        for a in range(lo, hi + 1):
            if ok(a):
                return a, True
        return None, True
    if not ok(hi):
        return None, False
    while lo < hi:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo, False  # invariant: ok(lo) holds (lo == hi and hi was only set on success)


def best_radius(n, w, budget, m_list, s_list, L_list, a_lo=None, exact=False, verbose=False,
                exhaustive_limit=EXHAUSTIVE_LIMIT):
    """For each (m,s,L) search the least a passing both gates; report the best (smallest a).

    Every returned a is certified (both gates pass there).  It is the least certified agreement
    over the grid only when info['least_proved'] is True, i.e. every family was searched
    exhaustively (see `least_passing`); otherwise it is a bisection candidate.  None means no
    certified radius was found, which proves none exists only when every family was exhaustive
    (info is unavailable then; the caller sees None)."""
    best = None
    all_exhaustive = True
    for m in m_list:
        for s in s_list:
            for L in L_list:
                lo, hi = (a_lo or (w + 1)), n

                def ok(a):
                    return certify(n, w, a, m, s, L, budget, exact=exact)[0]
                a, proved = least_passing(ok, lo, hi, exhaustive_limit)
                all_exhaustive = all_exhaustive and proved
                if a is None:
                    if verbose:
                        print(f"    m={m} s={s} L={L}: no certified radius "
                              f"({'exhaustive' if proved else 'endpoint fails; not searched'})",
                              flush=True)
                    continue
                info = certify(n, w, a, m, s, L, budget, exact=exact)[1]
                info['search'] = 'exhaustive' if proved else 'bisection (not proved least)'
                if verbose:
                    print(f"    m={m} s={s} L={L}: a={a} delta={1 - a / n:.6f} "
                          f"seeds<=2^{math.log2(info['seeds']):.2f} rank={info['rank']} "
                          f"[{info['search']}]", flush=True)
                if best is None or a < best[0]:
                    best = (a, m, s, L, info)
    if best is not None:
        best[4]['least_proved'] = all_exhaustive
    return best


def main():
    fails = []
    print("== 1. reproduce the PR #122 ledger at its own profile")
    n, w, a, m, s, L = 262144, 131071, 185354, 13, 3, 169
    total, gap, seeds = ledger(n, w, a, m, s, L)
    print(f"  totalNumerator = {total}  (Lean: 228788847483348849235588882)  "
          f"{'OK' if total == 228788847483348849235588882 else 'DIFF'}")
    if total != 228788847483348849235588882:
        fails.append("PR #122 totalNumerator")
    if gap * gap != 2946644089:
        fails.append("PR #122 gap^2")
    print(f"  gap^2 = {gap * gap} (Lean 2946644089); seeds <= {seeds:.6e} < 1e17: {total < 10**17 * gap * gap}")
    lcr = local_contact_rank(m, s, L)
    print(f"  localContactRank closed form = {lcr} (Lean 49960) {'OK' if lcr == 49960 else 'DIFF'}")
    if lcr != 49960:
        fails.append("PR #122 localContactRank")
    ok, dq, r = interpolation_ok(n, w, a, m, s, L, exact=True)
    print(f"  exact block rank = {r}, dimQ = {dq}, gate ok = {ok}")
    if r != lcr:
        fails.append("PR #122 exact block rank vs closed form")

    print("\n== 2. closed form vs exact block rank at other (m,s,L) (must agree)")
    for (m2, s2, L2, a2) in [(8, 2, 40, 186000), (12, 3, 80, 185000), (16, 4, 60, 184500),
                             (10, 5, 30, 186000)]:
        r_exact, _, _ = line_rank_blocks(m2 * a2, w, s2, L2, m2)
        r_cf = local_contact_rank(m2, s2, L2)
        print(f"  m={m2} s={s2} L={L2}: exact={r_exact} closed={r_cf} {'OK' if r_exact == r_cf else 'DIFF'}")
        if r_exact != r_cf:
            fails.append(f"rank m={m2} s={s2} L={L2}")

    print("\n== 3. koalaIRS12 budget (q = p^6, p = 2130706433): B <= q/2^129 (adapter gate 2^128*(B+B) <= q)")
    q6 = 2130706433 ** 6
    B_koala = q6 // (2 ** 129)
    print(f"  q = 2^{math.log2(q6):.2f}, budget B = 2^{math.log2(B_koala):.2f}")
    best = best_radius(n, w, B_koala, m_list=[9, 11, 13, 15, 17], s_list=[2, 3, 4],
                       L_list=[100, 140, 169, 200, 260], verbose=True)
    if best is None:
        print("  BEST: no certified radius found on this grid (bisection search; not a proof "
              "that none exists)")
        fails.append("section 3 found no certified radius")
    else:
        a_b, m_b, s_b, L_b, info = best
        AJ = math.isqrt(n * w) + 1
        tag = ("least certified a on this grid" if info['least_proved']
               else "certified a; bisection candidate, NOT proved least on this grid")
        print(f"  BEST: a={a_b} (Johnson floor {AJ}, beyond by {AJ - a_b}), "
              f"delta={1 - a_b / n:.6f}, m={m_b} s={s_b} L={L_b}, "
              f"seeds<=2^{math.log2(info['seeds']):.2f}  [{tag}]")

    print("\n== 4. prize-scale prime field: n = 2^30, w = 2^29 - 1, |F| ~ 2^250, budget 2^122")
    n3, w3 = 1 << 30, (1 << 29) - 1
    AJ3 = math.isqrt(n3 * w3) + 1
    print(f"  Johnson agreement floor {AJ3} = {AJ3 / n3:.6f} n  (delta_J = {1 - AJ3 / n3:.6f})")
    for (m3, s3, L3) in [(64, 16, 4096), (128, 32, 8192), (256, 64, 16384), (256, 64, 65536)]:
        # closed-form rank (validated above) to keep this fast; ledger for the count.
        # The range is far above EXHAUSTIVE_LIMIT, so this is a bisection candidate: a certified
        # radius, not a proved least one (the joint predicate is not monotone in a).
        def ok(a):
            return certify(n3, w3, a, m3, s3, L3, 1 << 122, exact=False)[0]
        lo, proved = least_passing(ok, w3 + 1, n3)
        if lo is None:
            print(f"  m={m3} s={s3} L={L3}: no certified radius found "
                  f"({'exhaustive' if proved else 'endpoint fails; not searched'})")
            continue
        info = certify(n3, w3, lo, m3, s3, L3, 1 << 122, exact=False)[1]
        print(f"  m={m3} s={s3} L={L3}: a={lo} = {lo / n3:.6f} n, delta={1 - lo / n3:.6f} "
              f"(beyond Johnson by {AJ3 - lo} positions), seeds<=2^{math.log2(info['seeds']):.2f}"
              f"  [{'least' if proved else 'certified; bisection candidate, not proved least'}]")

    if fails:
        print(f"\nFAIL: {len(fails)} regression check(s) failed: {fails}")
        raise SystemExit(1)
    print("\nPASS: PR #122 reproduction and closed-form/exact rank checks")


if __name__ == "__main__":
    main()
