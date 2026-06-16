#!/usr/bin/env python3
"""
#407 NOVEL-TOOL probe: Bourgain-Demeter-Guth decoupling / Vinogradov Mean Value Theorem (VMT).

QUESTION (assigned novel angle): the deep moment
    kappa_r = (1/m) sum_{c in Z/m} | sum_{j in Z/m} a_j e(-jc/m) |^{2r},   a_j = tau(chi^j)/sqrt q,
is the 2r-th mean value of an exponential sum over Z/m. VMT/decoupling sharply bound the 2r-th
moment of  sum_{x<=N} e(P(x))  for P a fixed-degree POLYNOMIAL. So: is arg(a_j) a bounded-degree
polynomial / algebraic phase in j (mod 1)? If yes, VMT could give kappa_r <= the diagonal to depth
r ~ ln m and CLOSE the floor. If no, VMT is inapplicable -- and we must say precisely why.

VERDICT (this probe): NO on three independent counts ->  VMT/decoupling is INAPPLICABLE.

  (A) No bounded-degree polynomial phase. The d-th forward difference of arg(a_j) over Z/m is never
      circularly constant for any d <= 6 (spread stays ~0.5-0.9, the random/equidistributed value).
  (B) The 2-cocycle is not bilinear. arg J(chi^i, chi^j) (the Jacobi-sum phase, = the deviation of
      arg(a_j) from additivity) is non-bilinear at ~95% of (i,j) pairs -> arg(a_j) is not even
      quadratic.
  (C) Sup-norm carries a growing log. sup/sqrt(m) GROWS (1.1 -> 2.4) while sup/sqrt(m ln m) is
      ~stable (1.0-1.5). A true bounded-degree poly phase makes VMT TIGHT at the diagonal value
      sqrt(m) with NO log; the observed log factor certifies a_j is NOT a poly phase.
  (E) Wrong averaging dimension. kappa_r averages ONLY the linear coefficient (c/m); the quadratic+
      coefficients of any phase are PINNED, not averaged. VMT's deg>=2 gain requires averaging the
      high coefficients. So even a HYPOTHETICAL poly phase reduces to degree-1 VMT = J_{r,1} = the
      (2r-1)!! n^r diagonal we already have -- it does NOT beat the existing moment-arrow wall.

Run:  python3 scripts/probes/_407_vmt_decoupling_phase.py
"""
import cmath, math
import numpy as np


def primitive_root(p):
    def order(g):
        o, x = 1, g % p
        while x != 1:
            x = (x * g) % p
            o += 1
            if o > p:
                return -1
        return o
    for g in range(2, p):
        if order(g) == p - 1:
            return g
    return None


def build(p, n):
    m = (p - 1) // n
    g = primitive_root(p)
    dlog = {}
    x = 1
    for k in range(p - 1):
        dlog[x] = k
        x = (x * g) % p

    def chi(j, xx):
        return cmath.exp(2j * math.pi * ((j * dlog[xx]) % m) / m)

    def tau(j):
        return sum(chi(j, xx) * cmath.exp(2j * math.pi * xx / p) for xx in range(1, p))

    sq = math.sqrt(p)
    a = [tau(j) / sq for j in range(m)]

    def J(i, j):
        s = 0 + 0j
        for xx in range(1, p):
            y = (1 - xx) % p
            if y == 0:
                continue
            s += chi(i, xx) * chi(j, y)
        return s

    return m, a, J


def fdiff_circular_spread(theta, d):
    arr = list(theta)
    for _ in range(d):
        arr = [(arr[i + 1] - arr[i]) % 1.0 for i in range(len(arr) - 1)]
    if not arr:
        return None
    c = np.exp(2j * np.pi * np.array(arr))
    return 1 - abs(c.mean())  # 0 => that difference is constant => poly of that degree-1


def main():
    tests = [(137, 8), (337, 16), (673, 32), (929, 32), (1697, 32),
             (353, 32), (577, 64), (1153, 128), (1409, 128)]

    print("== (A) is arg(a_j) a bounded-degree polynomial in j (Z/m)? "
          "[flat-at == degrees where it would be] ==")
    for (p, n) in tests:
        m, a, J = build(p, n)
        if m < 8:
            print(f"  p={p} n={n} m={m}: too small for diff test")
            continue
        theta = [(cmath.phase(a[j]) / (2 * math.pi)) % 1.0 for j in range(1, m)]
        sp = [fdiff_circular_spread(theta, d) for d in range(1, 7)]
        flat = [d for d in range(1, 7) if sp[d - 1] is not None and sp[d - 1] < 0.02]
        print(f"  p={p} n={n} m={m}: spreads(d=1..6)="
              f"{['%.2f' % s for s in sp]}  flat-at={flat}")

    print("\n== (B) is the Jacobi-sum phase bilinear (would make arg(a_j) quadratic)? "
          "[violation frac] ==")
    for (p, n) in tests:
        m, a, J = build(p, n)
        if m < 7:
            continue
        viol = tot = 0
        for i in range(1, m - 1):
            for j in range(1, m - 1):
                if (i + 1) % m == 0 or (i + 1 + j) % m == 0 or (i + j) % m == 0:
                    continue
                d = (cmath.phase(J((i + 1) % m, j)) - cmath.phase(J(i, j))
                     - cmath.phase(J(1, j))) / (2 * math.pi) % 1.0
                d = min(d, 1 - d)
                tot += 1
                viol += d > 0.02
        print(f"  p={p} n={n} m={m}: bilinearity-violation = {viol/tot:.3f}")

    print("\n== (C) sup-norm: sqrt(m) (VMT diagonal, no log) vs observed (carries growing log) ==")
    for (p, n) in tests:
        m, a, J = build(p, n)
        best = max(abs(sum(a[j] * cmath.exp(-2j * math.pi * (j * c) / m)
                           for j in range(m))) for c in range(m))
        print(f"  p={p} n={n} m={m}: sup={best:8.3f}  sup/sqrt(m)={best/math.sqrt(m):.3f}  "
              f"sup/sqrt(m ln m)={best/math.sqrt(m*math.log(max(m,2))):.3f}")


if __name__ == "__main__":
    main()
