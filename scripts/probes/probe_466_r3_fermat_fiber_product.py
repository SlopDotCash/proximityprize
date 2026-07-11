#!/usr/bin/env python3
"""
#466 r=3 R304: the off-diagonal quadruple sum via Fermat fiber products —
exact identities, Möbius stratum accounting, and the per-variety Weil NO-GO.

Objects (m = 3u', p == 1 mod m, chi = lambda^k order m):
  T_alpha = sum_{ind t == alpha (m), t != 0,1} chi(1-t)
  M4T     = sum_alpha |T_alpha|^4          (per-character 4th moment of T)

TESTS:
 (V1) TORUS/FIBER-PRODUCT IDENTITY (direct enumeration, small p):
        m^3 * M4T = sum over (t,x,y,z) in (F_p^*)^4, t*x^m,t*y^m,t*z^m,t != 1,
                    of chi( (1-t)(1-t x^m) / ((1-t y^m)(1-t z^m)) ).
      The "fixed variety" is a chi-weighted 4-DIMENSIONAL torus — its
      Weil/Deligne generic size is q^{4/2} = q^2 PER the whole sum, with
      Betti/Adolphson-Sperber constant ~ 4!Vol(Delta) ~ m^3.
 (V2) MOBIUS STRATUM ACCOUNTING (moderate p):
        sum_{k in (Z/m)^*} M4T^(k) = sum_{d|m} d mu(m/d) N4_d,
        N4_d = #{(t1,t2,s1,s2) in C_alpha^4 (some alpha):
                 (1-t1)(1-t2)/((1-s1)(1-s2)) in (F_q^*)^d}.
      Strata sizes: N4_d ~ q^4/(m^3 d) — the q^4 top terms CANCEL under
      sum d*mu(m/d) (same Mobius mechanism as the sextic); the surviving
      signal is q^2-scale while each N4_d's own Weil error lives at
      q^{7/2}-scale (dim-4 middle cohomology) — measured below.
 (V3) NO-GO NUMBERS: torus-sum/q^2 measured vs the A-S ceiling m^3 vs the
      family-cancellation truth ~ m^2 (equivalently K4 = O(1)); the
      per-variety route's floor is K4 = O(m) at EVERY q — no q-threshold,
      no unconditional prize-scale discharge from fixed-variety Weil.
 (V4) K_off CALIBRATION for the Lean-named input `OffDiagQuadrupleBound`:
        K_off = | sum_c |W(c)|^2 - diagR | / (m^2 q^2),
        W(c) = sum_{j!=0,c-j!=0} J_j J_{c-j},
        diagR = 2*(sum_{j!=0}|J_j|^2)^2 - sum_{j!=0}|J_j|^4,
      at m = 9, 12, 15, 18 over all primes <= 1200 (canonical chi).
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

def build(p, m):
    g = primitive_root(p)
    ind = {}
    x = 1
    for r in range(p - 1):
        ind[x] = r
        x = (x * g) % p
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    return ind, zm

def T_all(p, m, k, ind, zm):
    T = [0j] * m
    for t in range(2, p):
        T[ind[t] % m] += zm[(k * ind[(1 - t) % p]) % m]
    return T

def torus_sum(p, m, k, ind, zm):
    """direct (t,x,y,z) enumeration of the chi-weighted 4-torus (V1 RHS)"""
    # precompute x^m table and the residues 1 - t*x^m
    powm = [pow(x, m, p) for x in range(p)]
    s = 0j
    for t in range(1, p):
        if t == 1:
            continue
        # group x by value of t*x^m: multiplicity of each m-power class
        # t*x^m takes each value t*c (c an m-th power) exactly m times... enumerate x
        vals = {}
        for x in range(1, p):
            v = (t * powm[x]) % p
            vals[v] = vals.get(v, 0) + 1
        num_t = (1 - t) % p
        for v2, c2 in vals.items():
            if v2 == 1:
                continue
            a2 = (1 - v2) % p
            for v3, c3 in vals.items():
                if v3 == 1:
                    continue
                inv3 = pow((1 - v3) % p, p - 2, p)
                for v4, c4 in vals.items():
                    if v4 == 1:
                        continue
                    inv4 = pow((1 - v4) % p, p - 2, p)
                    arg = (num_t * a2 * inv3 * inv4) % p
                    s += c2 * c3 * c4 * zm[(k * ind[arg]) % m]
    return s

def mobius_strata(p, m, ind, zm):
    """(V2): LHS = sum_k M4T^(k); RHS strata N4_d by direct enumeration."""
    ks = [k for k in range(1, m) if math.gcd(k, m) == 1]
    lhs = 0.0
    for k in ks:
        T = T_all(p, m, k, ind, zm)
        lhs += sum(abs(t) ** 4 for t in T)
    cosets = [[] for _ in range(m)]
    for t in range(2, p):
        cosets[ind[t] % m].append(t)
    divs = [d for d in range(1, m + 1) if m % d == 0]
    N = {d: 0 for d in divs}
    for alpha in range(m):
        C = cosets[alpha]
        indr = [ind[(1 - t) % p] for t in C]
        n = len(C)
        for i1 in range(n):
            for i2 in range(n):
                a = indr[i1] + indr[i2]
                for i3 in range(n):
                    b = a - indr[i3]
                    for i4 in range(n):
                        r = b - indr[i4]
                        for d in divs:
                            if r % d == 0:
                                N[d] += 1
    rhs = sum(d * mobius(m // d) * N[d] for d in divs)
    return lhs, rhs, N

def quad_data(p, m, k, ind, zm):
    """(V4): K_off from the Jacobi ladder."""
    J = [sum(zm[(j * ind[t]) % m] * zm[(k * ind[(1 - t) % p]) % m]
             for t in range(2, p)) for j in range(m)]
    W = [sum(J[j] * J[(c - j) % m] for j in range(1, m) if (c - j) % m != 0)
         for c in range(m)]
    tot = sum(abs(w) ** 2 for w in W)
    s2 = sum(abs(J[j]) ** 2 for j in range(1, m))
    s4 = sum(abs(J[j]) ** 4 for j in range(1, m))
    diagR = 2 * s2 ** 2 - s4
    return abs(tot - diagR) / (m ** 2 * p ** 2), tot, diagR

def main():
    print(__doc__.splitlines()[1])
    # (V1) small-p direct torus enumeration
    print("\n(V1) torus/fiber-product identity, direct (t,x,y,z) enumeration:")
    for m, ps in ((9, (19, 37)), (12, (13, 37)), (15, (31,)), (18, (19, 37))):
        for p in ps:
            ind, zm = build(p, m)
            T = T_all(p, m, 1, ind, zm)
            lhs = m ** 3 * sum(abs(t) ** 4 for t in T)
            rhs = torus_sum(p, m, 1, ind, zm)
            ok = abs(lhs - rhs) < 1e-6 * max(1.0, abs(lhs))
            print(f"  m={m:>2} p={p:>3}: m^3*M4T = {lhs:14.4f}  torus = "
                  f"{rhs.real:14.4f}{rhs.imag:+.1e}i  "
                  f"|torus|/q^2 = {abs(rhs)/p**2:8.3f} (A-S ceiling ~ m^3 = {m**3})"
                  f"  {'OK' if ok else 'FAIL'}")
    # (V2) Mobius strata
    print("\n(V2) Mobius stratum accounting (moderate p): LHS = sum_d d*mu(m/d)*N4_d;")
    print("     top strata N4_d ~ q^4/(m^3 d) cancel; residual signal is q^2-scale;")
    print("     per-variety fluctuation of N4_d measured against q^{7/2}/(m^3 d):")
    for m, ps in ((9, (37, 73, 109, 163, 199)), (12, (37, 61, 97, 157, 193))):
        for p in ps:
            ind, zm = build(p, m)
            lhs, rhs, N = mobius_strata(p, m, ind, zm)
            ok = abs(lhs - rhs) < 1e-4 * max(1.0, abs(lhs))
            dev = max(abs(N[d] - p ** 4 / (m ** 3 * d)) / (p ** 3.5 / (m ** 3 * d))
                      for d in N)
            print(f"  m={m:>2} p={p:>4}: avg4th = {lhs:14.2f} mobius = {rhs:14.2f} "
                  f"{'OK' if ok else 'FAIL'}; signal/q^2 = {lhs/p**2:7.3f}; "
                  f"max stratum |N-main|/(q^3.5/(m^3 d)) = {dev:6.3f} "
                  f"(error scale q^3.5 >> signal q^2: NO main/error split)")
    # (V4) K_off calibration
    print("\n(V4) K_off = |quad_total - diagR|/(m^2 q^2) (canonical chi):")
    for m in (9, 12, 15, 18):
        primes = [p for p in range(m + 1, 1200)
                  if p % m == 1 and all(p % r for r in range(2, int(math.isqrt(p)) + 1))]
        Ks = []
        for p in primes:
            ind, zm = build(p, m)
            K, tot, diagR = quad_data(p, m, 1, ind, zm)
            Ks.append(K)
        print(f"  m={m:>2}: {len(primes)} primes; K_off max = {max(Ks):.3f}, "
              f"median = {sorted(Ks)[len(Ks)//2]:.3f} "
              f"(unconditional ceiling m+2 = {m+2}; open target O(1))")

if __name__ == "__main__":
    main()
