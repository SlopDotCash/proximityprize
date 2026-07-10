#!/usr/bin/env python3
"""r395 probe: certificate values + identity sanity for the coset-side fourth moment.

For H = {x^m : x in F_p^*} (the m-th powers), n = (p-1)/m, verifies with EXACT
integer counts (ordered tuples, same conventions as the Lean defs in
_R395MellinFourthMomentHBKTrim.lean):

  quadEnergy  E(H) = #{(x1,x2,x3,x4) in H^4 : x1+x2 = x3+x4 mod p}
  tripleCount T(H) = #{(x,y,z)      in H^3 : x+y  = z      mod p}
  dTerm       D    = n if -1 in H else 0

and then numerically checks the depth-2 identity (r341 dictionary; verified to
~1e-15 in the session's r5_moments.py, re-checked here independently):

  p(p-1) * sum_{t in mu_m} |M(t)|^4
      = m * (m^4 E + 4 m^3 T + 2 m^2 D + 4 m^2 n + 1 - p^3)

where M(chi(a)) = (m*S_a + 1)/sqrt(p), S_a = sum_{x in aH} e_p(x).
"""
import cmath
import math

def mth_powers(p, m):
    return sorted({pow(x, m, p) for x in range(1, p)})

def quad_energy(p, H):
    from collections import Counter
    r = Counter()
    for a in H:
        for b in H:
            r[(a + b) % p] += 1
    return sum(v * v for v in r.values())

def triple_count(p, H):
    Hs = set(H)
    return sum(1 for a in H for b in H if (a + b) % p in Hs)

def fourth_moment_lhs(p, m, H):
    # M over mu_m via cosets: coset reps a run over F_p^* / H; M value depends
    # only on the coset. Sum over ALL a in F_p^* of |M|^4 counts each coset
    # value n times; sum over mu_m = (1/n) * sum over a.
    n = (p - 1) // m
    tot = 0.0
    e = lambda x: cmath.exp(2j * cmath.pi * x / p)
    for a in range(1, p):
        S_a = sum(e((a * x) % p) for x in H)
        M = (m * S_a + 1) / math.sqrt(p)
        tot += abs(M) ** 4
    return tot / n  # = sum over t in mu_m

def main():
    for (p, m) in [(13, 4), (29, 7), (41, 10), (61, 12)]:
        H = mth_powers(p, m)
        n = (p - 1) // m
        assert len(H) == n, (p, m, len(H), n)
        E = quad_energy(p, H)
        T = triple_count(p, H)
        D = n if (p - 1) in H else 0
        lhs = p * (p - 1) * fourth_moment_lhs(p, m, H)
        rhs = m * (m**4 * E + 4 * m**3 * T + 2 * m**2 * D + 4 * m**2 * n + 1 - p**3)
        rel = abs(lhs - rhs) / max(1.0, abs(rhs))
        print(f"p={p:3d} m={m:3d} n={n:2d} H={H} E={E} T={T} D={D} "
              f"negOneInH={(p-1) in H} idRelErr={rel:.2e}")
        assert rel < 1e-9, (p, m, lhs, rhs)
    print("identity + certificate values OK")

if __name__ == "__main__":
    main()
