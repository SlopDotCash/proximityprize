#!/usr/bin/env python3
"""G103: centered triple-sum concentration of mu_n — the minimal post-G102 certificate.

G102 proves depth 5 of the padded collision lane is out of reach of (cardinality, pair-sum
concentration).  The minimal upgrade is the TRIPLE-sum concentration M3 = max_a N3(a),
N3(a) = #{(h1,h2,h3) in H^3 : h1+h2+h3 = a}.  Chain: J5 <= M3 * n^7, closing at M3 <= 2^25.82.

FINDING 1 (raw M3 is degenerate at production): for even n, -1 in mu_n, so every a in H has
the antipodal family h + (y - y) = a: N3(a) >= 3n - O(1).  At n = 2^30 (even), raw
M3 >= 3n = 2^31.6 > threshold 2^25.8 — raw triple concentration CANNOT close depth 5.

FINDING 2 (centered M3 collapses): excluding triples containing an antipodal pair
(h_i + h_j = 0), the centered concentration M3^cent measures O(1) (6..18 across all tested
scales; 6 = 3! = a single unordered genuine solution).  The degenerate mass is exactly
supported on H with mass 3n - 3 per point (inclusion-exclusion on double antipodal pairs),
so the consumer split

    J5 <= 2 * M3cent * n^7 + 18 * M2 * n^6

absorbs it with the KNOWN Stepanov pair bound M2 <= 4n^{2/3}; closure needs only
M3cent <= 2^24 (empirical truth: O(1); headroom 2^20+).

This script measures raw vs centered M3 for real subgroups mu_n in F_p, n ~ p^{1/4}, and
verifies the exact degenerate-mass formula N3deg(a) = (3n - 3) * 1_{a in H} for even n.
"""

import math
from collections import Counter


def sieve(limit):
    s = [True] * (limit + 1)
    s[0] = s[1] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, limit + 1, i):
                s[j] = False
    return [i for i, v in enumerate(s) if v]


def subgroup(p, m):
    for c in range(2, 300):
        x = pow(c, (p - 1) // m, p)
        if pow(x, m, p) != 1:
            continue
        mm, qs = m, set()
        d = 2
        while d * d <= mm:
            if mm % d == 0:
                qs.add(d)
                while mm % d == 0:
                    mm //= d
            d += 1
        if mm > 1:
            qs.add(mm)
        if all(pow(x, m // q, p) != 1 for q in qs):
            H, h = [], 1
            for _ in range(m):
                H.append(h)
                h = h * x % p
            return H
    return None


def main():
    primes = sieve(3000000)
    cases, seen = [], set()
    for p in primes:
        if p < 20000:
            continue
        n = round(p ** 0.25)
        for m in range(max(6, n - 6), n + 7):
            if (p - 1) % m == 0 and m % 2 == 0:
                k = int(math.log2(p))
                if k not in seen:
                    seen.add(k)
                    cases.append((p, m))
                break
    print(f"{'p':>9} {'n':>4}  {'rawM3':>6} {'3n-3':>5}  {'centM3':>6}  {'degOK':>5}  "
          f"{'thresh n^0.86':>13}")
    for p, m in cases[:8]:
        H = subgroup(p, m)
        if H is None:
            continue
        Hset = set(H)
        c3, c3c, c3d = Counter(), Counter(), Counter()
        for a in H:
            for b in H:
                ab = (a + b) % p
                dab = ab == 0
                for cc in H:
                    s = (ab + cc) % p
                    c3[s] += 1
                    if dab or (b + cc) % p == 0 or (a + cc) % p == 0:
                        c3d[s] += 1
                    else:
                        c3c[s] += 1
        raw = max(v for k, v in c3.items() if k != 0)
        cent = max((v for k, v in c3c.items() if k != 0), default=0)
        # verify exact degenerate mass formula on H
        deg_ok = all(c3d.get(h, 0) == 3 * m - 3 for h in Hset) and \
            all(k in Hset or k == 0 for k in c3d)
        print(f"{p:>9} {m:>4}  {raw:>6} {3*m-3:>5}  {cent:>6}  {str(deg_ok):>5}  "
              f"{m ** 0.86:>13.1f}")


if __name__ == "__main__":
    main()
