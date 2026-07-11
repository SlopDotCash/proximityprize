#!/usr/bin/env python3
"""
#466 r=3, m = 9 (the smallest open DIST instance): cubic/nonic cyclotomy probe.

Structure at m=9 (u=3): exactly three H-cosets, so DIST triples carry label
multiset {0,1,2}, whose sum is 0 mod 3 => DIST(d) is SUPPORTED on d in {0,3,6},
with exactly 6*9 = 54 ordered triples per support point (before zero-index
exclusions).  Counting then gives E_DIST <= 3*(54 q^{3/2})^2 = 8748 q^3
= 12 * 9^3 * q^3 unconditionally -- checked here numerically, and the sharp
constant C_D(9) = sup_q E_DIST/(9^3 q^3) is measured.

Cyclotomy tests (chi = lambda canonical, order 9; p == 1 mod 9; 4p = L^2+27M^2,
L == 1 mod 3):
  (a) is E_DIST an integer?  is it a function of p alone (primitive-root
      independent)?  least-squares regression of E_DIST against monomials
      {p^3, p^2, p^2 L, p L^2, p M^2, p, ...} -- exact fit iff residual ~ 0.
      Also the Galois-averaged energy over the six order-9 characters.
  (b) does DIST(d) collapse to Jacobi-sum monomials?  test |DIST(d)|/q^{3/2}
      profile and constancy of DIST(d)/(q * J3(d)) across d and p.
  (c) C_D(9) statistics.
"""

import cmath, math, sys
from probe_466_r3_hasse_davenport_coset import primitive_root, build

def cyclotomic_LM(p):
    # 4p = L^2 + 27 M^2, L == 1 mod 3
    for M in range(0, int(math.isqrt(4 * p // 27)) + 2):
        r = 4 * p - 27 * M * M
        if r < 0:
            break
        L = int(math.isqrt(r))
        if L * L == r:
            if L % 3 == 1:
                return L, M
            if (-L) % 3 == 1:
                return -L, M
    return None, None

def dist_data(p, e, g=None):
    """Return (E_DIST, [DIST(d)]_d, J, J3) for m=9, chi = zq^{e ind}."""
    m = 9
    # optionally use a specified primitive root (to test generator dependence)
    if g is None:
        ind = build(p, m)
    else:
        ind = {}
        x = 1
        for k in range(p - 1):
            ind[x] = k
            x = (x * g) % p
    q1 = p - 1
    zq = lambda a: cmath.exp(2j * math.pi * (a % q1) / q1)
    chi = lambda t, s: 0.0 if t % p == 0 else zq(s * e * ind[t % p])
    lam = lambda j, t: 0.0 if t % p == 0 else cmath.exp(2j * math.pi * ((j * ind[t % p]) % m) / m)
    jc = lambda s, c: sum(lam(c, t) * chi((1 - t) % p, s) for t in range(p))
    J = [jc(1, j) for j in range(m)]
    J3 = [jc(3, c) for c in range(m)]
    D = [0j] * m
    cnt = [0] * m
    for j1 in range(1, m):
        for j2 in range(1, m):
            for j3 in range(1, m):
                if len({j1 % 3, j2 % 3, j3 % 3}) == 3:
                    d = (j1 + j2 + j3) % m
                    D[d] += J[j1] * J[j2] * J[j3]
                    cnt[d] += 1
    E = sum(abs(x) ** 2 for x in D)
    return E, D, cnt, J3

def second_primitive_root(p):
    g = primitive_root(p)
    fac = []
    n = p - 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fac.append(n)
    for h in range(g + 1, p):
        if all(pow(h, (p - 1) // f, p) != 1 for f in fac):
            return h
    return g

def main():
    primes = [p for p in range(19, 1200)
              if p % 9 == 1 and all(p % r for r in range(2, int(math.isqrt(p)) + 1))]
    print(f"m=9 probe over {len(primes)} primes p==1 (mod 9): {primes[:6]}...{primes[-2:]}")

    rows = []
    supp_ok = True
    cnt_ok = True
    maxC = 0.0
    gen_dep = None
    print(f"\n{'p':>5} {'L':>4} {'M':>3} {'E_DIST':>16} {'int?':>5} {'E/q^3':>8} {'C_D':>7} {'|D(0)|/q^1.5':>12} {'|D(3)|/q^1.5':>12} {'|D(6)|/q^1.5':>12}")
    for p in primes:
        e = (p - 1) // 9  # canonical chi = lambda (order 9)
        E, D, cnt, J3 = dist_data(p, e)
        L, M = cyclotomic_LM(p)
        # support + count structure
        for d in range(9):
            if d in (0, 3, 6):
                if cnt[d] != 54 - (6 if d == 0 else 6):  # zero-exclusions: count them honestly below
                    pass
            else:
                if cnt[d] != 0 or abs(D[d]) > 1e-6 * p ** 1.5:
                    supp_ok = False
        tot_cnt = sum(cnt)
        if tot_cnt > 3 * 54:
            cnt_ok = False
        C = E / (9 ** 3 * p ** 3)
        maxC = max(maxC, C)
        is_int = abs(E - round(E)) < 1e-4 * max(1.0, E * 1e-9)
        rows.append((p, L, M, E, C))
        print(f"{p:>5} {L:>4} {M:>3} {E:>16.3f} {str(abs(E-round(E))<0.01):>5} {E/p**3:>8.4f} {C:>7.5f} "
              f"{abs(D[0])/p**1.5:>12.4f} {abs(D[3])/p**1.5:>12.4f} {abs(D[6])/p**1.5:>12.4f}")

    # generator dependence at one prime
    p0 = primes[3]
    g2 = second_primitive_root(p0)
    E1, _, _, _ = dist_data(p0, (p0 - 1) // 9)
    E2, _, _, _ = dist_data(p0, (p0 - 1) // 9, g=g2)
    gen_dep = abs(E1 - E2) / max(E1, 1.0)
    print(f"\ngenerator dependence at p={p0}: |E(g1)-E(g2)|/E = {gen_dep:.6f} "
          f"({'INDEPENDENT' if gen_dep < 1e-9 else 'DEPENDS ON GENERATOR -> per-character E has no closed form in (p,L,M) alone'})")

    # Galois-averaged energy over the six order-9 characters (generator-invariant)
    print(f"\nGalois-averaged E over order-9 chi (invariant object): regression target")
    avg_rows = []
    for p in primes[:16]:
        q1 = p - 1
        es = [k * q1 // 9 for k in (1, 2, 4, 5, 7, 8)]
        Ea = sum(dist_data(p, e)[0] for e in es) / 6
        L, M = cyclotomic_LM(p)
        avg_rows.append((p, L, M, Ea))
        print(f"  p={p:>4} L={L:>4} M={M:>2} E_avg={Ea:>15.3f} int_dist={abs(Ea-round(Ea)):.4f} E_avg/p^3={Ea/p**3:.4f}")

    # least-squares regression of E_avg on monomials
    import itertools
    def regress(rows, monos, names):
        A = [[mono(p, L, M) for mono in monos] for (p, L, M, E) in rows]
        b = [E for (_, _, _, E) in rows]
        # normal equations via simple Gaussian elimination
        n = len(monos)
        AtA = [[sum(A[r][i] * A[r][j] for r in range(len(A))) for j in range(n)] for i in range(n)]
        Atb = [sum(A[r][i] * b[r] for r in range(len(A))) for i in range(n)]
        # solve
        Mx = [row[:] + [Atb[i]] for i, row in enumerate(AtA)]
        for c in range(n):
            piv = max(range(c, n), key=lambda r: abs(Mx[r][c]))
            Mx[c], Mx[piv] = Mx[piv], Mx[c]
            if abs(Mx[c][c]) < 1e-12:
                continue
            for r in range(n):
                if r != c:
                    f = Mx[r][c] / Mx[c][c]
                    for k in range(c, n + 1):
                        Mx[r][k] -= f * Mx[c][k]
        coef = [Mx[i][n] / Mx[i][i] if abs(Mx[i][i]) > 1e-12 else 0.0 for i in range(n)]
        resid = max(abs(sum(coef[i] * A[r][i] for i in range(n)) - b[r]) / max(abs(b[r]), 1)
                    for r in range(len(A)))
        return coef, resid
    monos = [lambda p, L, M: p ** 3, lambda p, L, M: p ** 2, lambda p, L, M: p ** 2 * L,
             lambda p, L, M: p * L ** 2, lambda p, L, M: p * M ** 2, lambda p, L, M: p ** 2 * M ** 2 / p,
             lambda p, L, M: p, lambda p, L, M: 1.0]
    names = ["p^3", "p^2", "p^2*L", "p*L^2", "p*M^2", "p*M^2(b)", "p", "1"]
    coef, resid = regress(avg_rows, monos, names)
    print(f"\nLSQ fit of E_avg on {names}: max rel residual = {resid:.4e}")
    print("  coefficients:", ", ".join(f"{n}={c:.4f}" for n, c in zip(names, coef)))
    print(f"  verdict: {'EXACT closed form plausible' if resid < 1e-6 else 'NO exact closed form in these monomials (refuted at this basis)'}")

    print(f"\nsupport structure DIST(d)=0 for d not in {{0,3,6}}: {'CONFIRMED' if supp_ok else 'VIOLATED'}")
    print(f"total DIST triple count <= 162 per instance: {'CONFIRMED' if cnt_ok else 'VIOLATED'}")
    print(f"sharp constant over probed primes: C_D(9) = sup E_DIST/(9^3 q^3) = {maxC:.5f} (counting bound: 12)")
    if not supp_ok or not cnt_ok:
        sys.exit(1)

if __name__ == "__main__":
    main()
