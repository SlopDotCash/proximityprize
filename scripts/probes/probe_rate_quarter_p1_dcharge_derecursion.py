#!/usr/bin/env python3
"""Probe: the D-charge derecursion parameter flow (exact P1 integers).

The derecursion discovered in the global-consistency round, made precise:

Level 0 (pairs -> directions). For pencils through one base (gamma0, p0):
  w0 = p0 - gamma0*w1 (the direction w1 DETERMINES the pencil), and
  alignedSet = {D = 0} cap {w1 = u1}  (A = agreement of the direction with u1
  on Z = {D=0}).  Riders <= F/(T-A) with the SHARED pool F = N - |Z|; riders
  <= F unconditionally (each rider needs >= 1 pool vote).

Level 1 (the flow map). Every bad gamma != gamma0 maps injectively via
  s = 1/(gamma - gamma0) to a scalar whose line u1 - s*D has the pencil
  direction w1 agreeing on >= T coordinates (aligned coords: D=0 so
  u1 - sD = u1 = w1; vote coords: the vote equation solves w1 = u1 - sD).
So #bad <= 1 + sum over directions w of r(w), r(w) <= F/(T - agrZ(w,u1)),
and contributing directions need agrZ >= T - F.

Level 2 (the dichotomy). The direction count at agreement level a on Z is
Johnson-bounded iff a^2 > |Z|(k-1) = (N-F)(k-1).  Since contributing levels
start at a = T-F, the WHOLE ledger is Johnson-counted iff
  (T-F)^2 > (N-F)(k-1)     ...  i.e. F below the small root F0 of
  x^2 - (2T-(k-1))x + T^2 - N(k-1) = 0.
For F > F0 the window [T-F, JohnsonZ] is nonempty: sub-Johnson-on-Z swarm =
the STALL.  This probe computes the exact boundary, the exact greedy ledger
optimum for F <= F0 (is the small-F branch actually <= N?), and the stall
window data.
"""

import math
from fractions import Fraction

N = 2**30
K = 2**28
T = 592794966


def isqrt(x):
    return math.isqrt(x)


def johnson_count(a, n_dom, k):
    """Exact-diagonal Johnson: max family size at agreement level >= a with
    pairwise <= k-1, domain n_dom: L <= n_dom*(a-(k-1)) / (a^2 - n_dom*(k-1)),
    valid when denominator > 0."""
    den = a * a - n_dom * (k - 1)
    if den <= 0:
        return None  # unbounded by Johnson
    return (n_dom * (a - (k - 1))) // den


def main():
    print("== exact boundary of the derecursion dichotomy ==")
    # (T-F)^2 > (N-F)(k-1)  <=>  F^2 - (2T-(k-1))F + T^2 - N(k-1) > 0 (F < T)
    b = 2 * T - (K - 1)
    c = T * T - N * (K - 1)
    disc = b * b - 4 * c
    sq = isqrt(disc)
    F0 = (b - sq) // 2  # largest F with strict inequality: check exactly
    while (T - F0) ** 2 <= (N - F0) * (K - 1):
        F0 -= 1
    while (T - (F0 + 1)) ** 2 > (N - (F0 + 1)) * (K - 1):
        F0 += 1
    print(f"  F0 = {F0}: (T-F0)^2 - (N-F0)(k-1) = "
          f"{(T - F0)**2 - (N - F0) * (K - 1)} > 0")
    print(f"  at F0+1: (T-F)^2 - (N-F)(k-1) = "
          f"{(T - F0 - 1)**2 - (N - F0 - 1) * (K - 1)} <= 0")
    print(f"  three-heavy pool cap 100663294 vs F0: "
          f"{'BELOW' if 100663294 <= F0 else 'ABOVE'} the closure boundary")

    print("\n== greedy ledger optimum for F <= F0 (is the small-F branch <= N?) ==")
    # adversary: directions at levels a in [T-F, T-1] (a below T; a >= T handled
    # by threshold-list <= 5 with riders <= F each -- include them: at a >= T,
    # riders <= F (unconditional pool bound), count <= johnson at T).
    # ledger max = 1 + sum over levels of (count(a) - count(a+1)) * F/(T-a),
    # computed greedily from the top level down with exact integers.
    worst = (0, 0)
    for F in [F0, F0 - 1, F0 // 2, 10**7, 5 * 10**7, 7 * 10**7,
              74000000, 74500000, F0 - 100, F0 - 10]:
        if F < 1 or F > F0:
            continue
        Z = N - F
        total = 1
        prev_count = 0
        # levels above threshold: at most johnson_count(T) pencils, riders <= F
        cT = johnson_count(T, Z, K)
        total += cT * F
        prev_count = cT
        # levels a = T-1 down to T-F: riders per pencil <= F // (T - a)
        # greedy: at each level the Johnson count is the cap on the CUMULATIVE
        # family down to that level; marginal new pencils get the level's cap.
        a = T - 1
        while a >= T - F:
            cnt = johnson_count(a, Z, K)
            if cnt is None:
                print(f"  F={F}: level {a} below JohnsonZ -- should not happen")
                break
            new = max(0, cnt - prev_count)
            if new:
                total += new * (F // (T - a))
                prev_count = cnt
            # jump to next level where the count increases (binary-ish scan)
            a -= 1
            # speedup: skip levels with same count
            if new == 0 and cnt == prev_count:
                # find next a where count changes by stepping in chunks
                step = 1 << 20
                while a - step >= T - F and johnson_count(a - step, Z, K) == cnt:
                    a -= step
                while step > 1:
                    step >>= 1
                    while a - step >= T - F and \
                            johnson_count(a - step, Z, K) == cnt:
                        a -= step
        verdict = "<= N: CLOSED" if total <= N else "> N: NOT closed by ledger"
        print(f"  F = {F}: greedy ledger max = {total}  ({verdict})")
        if total > worst[1]:
            worst = (F, total)
    print(f"  worst case: F = {worst[0]}, total = {worst[1]}, N = {N}")

    print("\n== stall window ==")
    # for F in (F0, N-T]: window [T-F, JohnsonZ(F)] nonempty; for F > N-T the
    # pool exceeds the fiber cap N-T (old surface caps riders at N-T anyway).
    for F in [F0 + 1, 100663294, 2 * 10**8, N - T]:
        Z = N - F
        jz = isqrt(Z * (K - 1))
        lo = T - F
        print(f"  F = {F}: sterile below alignment {lo}; JohnsonZ = {jz}; "
              f"stall window width = {jz - lo if jz >= lo else 0}")

    print("\n== flow map sanity at mu_256/F_257 (end-to-end) ==")
    import random
    import numpy as np
    p, n, k = 257, 256, 64
    Ts = (53 * n) // 96 + 1
    rng = random.Random(11)
    # generator of F_257^*
    g = 3
    dom = [pow(g, i, p) for i in range(n)]
    V = np.zeros((k, n), dtype=np.int64)
    for j in range(k):
        V[j] = [pow(x, j, p) for x in dom]

    def randcw():
        cf = np.array([rng.randrange(p) for _ in range(k)], dtype=np.int64)
        return (cf @ V) % p

    ok = True
    for _ in range(100):
        u0 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        u1 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        g0 = rng.randrange(p)
        w1 = randcw()
        p0 = randcw()
        w0 = (p0 - g0 * w1) % p
        D = (p0 - u0 - g0 * u1) % p
        aligned = (w0 == u0) & (w1 == u1)
        # LEVEL-0 identity: aligned == {D = 0} & {w1 = u1}
        if not np.array_equal(aligned, (D == 0) & (w1 == u1)):
            ok = False
        # LEVEL-1 flow: for each gamma != g0, vote coords satisfy
        # w1 = u1 - s*D with s = 1/(gamma-g0), so agreement of w1 with
        # u1 - s*D contains aligned cup votes
        for gam in rng.sample([x for x in range(p) if x != g0], 6):
            s = pow((gam - g0) % p, p - 2, p)
            line_ok = (w0 + gam * w1) % p == (u0 + gam * u1) % p
            votes = line_ok & ~aligned
            vs = (u1 - s * D) % p
            agr = (w1 == vs)
            if np.any((aligned | votes) & ~agr):
                ok = False
    print(f"  level-0 aligned identity + level-1 flow-map inclusion over 100 "
          f"instances x 6 scalars: {'ALL OK' if ok else 'VIOLATIONS'}")
    assert ok


if __name__ == "__main__":
    main()


def mds_pool_second_charge():
    """MDS-pool regime (F >= k): the second charge and its collapse.

    Level-2 instance on the pool: stack (u1, -D), MDS code dim k length F,
    swarm riders have pool agreement >= t1 = T - JohnsonZ(F).  Exact facts:
    * t1 <= T - floor(sqrt(T(k-1))) = 193887475 < k-1 for EVERY F <= N-T
      (JohnsonZ decreasing in F, min at F = N-T since |Z| >= T);
    * threshold collapse: once the running threshold t < k-1, no Johnson
      condition can ever fire again: (t-F2)^2 <= t^2 < t(k-1) <= Z2(k-1)
      because every level's zero-set holds a base witness (Z2 >= t);
    * hence the iteration DOUBLE-STALLS at depth 2 in the whole MDS regime;
      combined two-Johnson band (J_Z + J_pool > T for all F in [k, N-T]).
    """
    print("\n== MDS-pool second charge (F in [k, N-T]) ==")
    j = isqrt(T * (K - 1))
    assert j == 398907491 and j * j <= T * (K - 1) < (j + 1) ** 2
    t1max = T - j
    print(f"  max level-2 threshold t1 = T - floor(sqrt(T(k-1))) = {t1max}")
    assert t1max == 193887475 and t1max < K - 1
    print(f"  threshold collapse: t1max = {t1max} < k-1 = {K - 1}  "
          f"-> level-2 Johnson can NEVER fire (t1^2 = {t1max**2} < "
          f"t1(k-1) = {t1max * (K - 1)})")
    # sweep the whole MDS regime: t1(F) < k-1 and band nonempty everywhere
    worst_band = None
    for F in range(K, N - T + 1, 2**22):
        jz = isqrt((N - F) * (K - 1))
        jp = isqrt(F * (K - 1))
        t1 = T - jz
        assert t1 < K - 1, F
        assert jz + jp > T, F  # two-Johnson band nonempty
        w = jz - (T - jp)
        if worst_band is None or w < worst_band[1]:
            worst_band = (F, w)
    for F in (K, N - T):  # endpoints exactly
        jz = isqrt((N - F) * (K - 1))
        jp = isqrt(F * (K - 1))
        assert T - jz < K - 1 and jz + jp > T
        print(f"  F = {F}: t1 = {T - jz}, band = ({T - jp}, {jz}], "
              f"width {jz - (T - jp)}")
    print(f"  narrowest band over sweep: width {worst_band[1]} at F = "
          f"{worst_band[0]}  (never empty)")
    print("  VERDICT: the derecursion terminates at depth 2 with a")
    print("  PERMANENT sub-Johnson stall throughout the MDS regime; the")
    print("  residual is beyond-Johnson list structure -- the prize wall.")


mds_pool_second_charge()
