#!/usr/bin/env python3
"""
#466 r=3 R303: fourth moment of the full Jacobi DFT — identity, main-term
structure, and the interpolation constant.

Objects (m = 3u', p == 1 mod m, lambda order m, chi = lambda^k):
  J_j    = J(lambda^j, chi);   S(a) = sum_{j != 0} zeta_m^{aj} J_j  (= "Shat")
  M4     = sum_a |S(a)|^4      (the fourth moment)
  W(c)   = sum_{j != 0, c-j != 0} J_j J_{c-j}   (zero-removed self-convolution)

TESTS:
 (F1) EXACT IDENTITY (the Lean-formalized core): M4 = m * sum_c |W(c)|^2 —
      the 4th moment IS the r=2 additive-quadruple energy.
 (F2) SCALE CHECK (refutes the m^2 q^2 target): the exact diagonal
      D = 2*(sum_{j!=0}|J_j|^2)^2 - sum_{j!=0}|J_j|^4 satisfies m*D ~ 2 m^3 q^2,
      so M4 >= ~2 m^3 q^2 is forced; correct flat scale is K4 * m^3 * q^2.
      Also power-mean floor M4 >= (sum_a |S|^2)^2 / m.
 (F3) MOBIUS AT 4TH MOMENT: diagonal weight sum_{d|m} d*mu(m/d) = phi(m) != 0
      (arithmetic check) — the main term is NOT killed, unlike the sextic.
 (F4) MEASURE K4 = M4/(m^3 q^2) per character and Galois-max, m = 9,12,15,18;
      off-diagonal share (M4/m - D)/D; and the interpolated DIST constant
      C_interp = (3*K4^1.5 + 1215)*sqrt(m) vs measured C_D*(actual).
"""

import cmath, math

def primitive_root(p):
    fac, n, d = [], p - 1, 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fac.append(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise ValueError

def mobius(n):
    r, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            if n % d == 0:
                return 0
            r = -r
        d += 1
    if n > 1:
        r = -r
    return r

def phi(n):
    r, d = n, 2
    while d * d <= n:
        if n % d == 0:
            r -= r // d
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        r -= r // n
    return r

def jacobi_ladder(p, m, k):
    g = primitive_root(p)
    ind = {}
    x = 1
    for r in range(p - 1):
        ind[x] = r
        x = (x * g) % p
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    return [sum(zm[(j * ind[t]) % m] * zm[(k * ind[(1 - t) % p]) % m]
                for t in range(2, p)) for j in range(m)]

def instance(p, m, k):
    J = jacobi_ladder(p, m, k)
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    S = [sum(zm[(a * j) % m] * J[j] for j in range(1, m)) for a in range(m)]
    M4 = sum(abs(s) ** 4 for s in S)
    M2 = sum(abs(s) ** 2 for s in S)
    W = [sum(J[j] * J[(c - j) % m] for j in range(1, m) if (c - j) % m != 0)
         for c in range(m)]
    rhs = m * sum(abs(w) ** 2 for w in W)
    s2 = sum(abs(J[j]) ** 2 for j in range(1, m))
    s4 = sum(abs(J[j]) ** 4 for j in range(1, m))
    D = 2 * s2 ** 2 - s4          # exact diagonal of the quadruple sum
    return M4, rhs, M2, D

def dist_energy(p, m, k):
    """direct E_DIST for comparison with the interpolated bound"""
    J = jacobi_ladder(p, m, k)
    u = m // 3
    Dd = [0j] * m
    for j1 in range(1, m):
        for j2 in range(1, m):
            for j3 in range(1, m):
                l1, l2, l3 = j1 % u, j2 % u, j3 % u
                if l1 != l2 and l1 != l3 and l2 != l3:
                    Dd[(j1 + j2 + j3) % m] += J[j1] * J[j2] * J[j3]
    return sum(abs(x) ** 2 for x in Dd)

def main():
    print(__doc__.splitlines()[1])
    for m in (9, 12, 15, 18):
        divs = [d for d in range(1, m + 1) if m % d == 0]
        wdiag = sum(d * mobius(m // d) for d in divs)
        print(f"\n===== m = {m}:  (F3) sum_(d|m) d*mu(m/d) = {wdiag} "
              f"(= phi(m) = {phi(m)}; nonzero => diagonal main term SURVIVES) =====")
        primes = [p for p in range(m + 1, 1200)
                  if p % m == 1 and all(p % r for r in range(2, int(math.isqrt(p)) + 1))]
        ks = [k for k in range(1, m) if math.gcd(k, m) == 1]
        print(f"{'p':>5} {'F1 id':>6} {'K4(chi=lam)':>11} {'K4 max/k':>9} "
              f"{'m*D/(m^3q^2)':>12} {'offdiag/diag':>12} {'pm-floor':>9} "
              f"{'C_interp':>9} {'C_D meas':>9}")
        ok_all = True
        K4max_m = 0.0
        for p in primes:
            scale = m ** 3 * p ** 2
            M4, rhs, M2, D = instance(p, m, 1)
            id_ok = abs(M4 - rhs) < 1e-6 * max(1.0, M4)
            K4s = []
            for k in ks:
                M4k, rhsk, M2k, Dk = instance(p, m, k)
                if abs(M4k - rhsk) > 1e-6 * max(1.0, M4k):
                    id_ok = False
                K4s.append(M4k / scale)
            K4 = M4 / scale
            K4max = max(K4s)
            K4max_m = max(K4max_m, K4max)
            ok_all = ok_all and id_ok
            pmfloor = (M2 ** 2 / m) / scale      # power-mean floor on K4
            offshare = (M4 / m - D) / D if D > 0 else float('nan')
            C_interp = (3 * K4 ** 1.5 + 1215) * math.sqrt(m)
            E = dist_energy(p, m, 1)
            C_meas = E / (m ** 3 * p ** 3)
            print(f"{p:>5} {str(id_ok)[0]:>6} {K4:>11.3f} {K4max:>9.3f} "
                  f"{m*D/scale:>12.3f} {offshare:>12.3f} {pmfloor:>9.3f} "
                  f"{C_interp:>9.1f} {C_meas:>9.4f}")
        print(f"  m={m}: (F1) identity {'VERIFIED' if ok_all else 'FAILED'}; "
              f"sup K4 over primes/characters = {K4max_m:.3f} "
              f"(diagonal forces K4 >~ 2; m^2 q^2 target IMPOSSIBLE, m^3 q^2 is the flat scale)")

if __name__ == "__main__":
    main()
