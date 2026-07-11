#!/usr/bin/env python3
"""
#466 r=3 DIST rung: trace-formula / point-count reformulation (Fu-Wan style).

Objects (m divisible by 3, u' = m/3; p == 1 mod m; lambda of order m; chi = lambda^k):
  J_j       = J(lambda^j, chi) = sum_t lambda^j(t) chi(1-t)
  DIST(d)   = sum over ordered triples (j1,j2,j3), j_i != 0, coset labels
              (j_i mod u') pairwise distinct, j1+j2+j3 = d, of J_{j1}J_{j2}J_{j3}
  E_DIST    = sum_d |DIST(d)|^2   (the open object: DistStratumEnergyBound)

IDENTITIES TESTED (all exact; numeric to machine precision):

 (I1) SPECTRAL/NEWTON (unconditional finite algebra; the Lean-formalized core):
        A_c(a) = sum_{j != 0, j == c mod u'} zeta_m^{aj} J_j     (c in Z/u')
        S(a)   = sum_c A_c(a),  P2(a) = sum_c A_c(a)^2,  P3(a) = sum_c A_c(a)^3
        Dhat(a) = S(a)^3 - 3 S(a) P2(a) + 2 P3(a)
        E_DIST = (1/m) sum_a |Dhat(a)|^2.

 (I2) MODE = POINT-RESTRICTED SUM:  S(a) = m*T_{-a} + 1, where
        T_alpha = sum_{t: ind(t) == alpha mod m, t != 0,1} chi(1-t).

 (I3) GALOIS-AVERAGED MODE ENERGY = MOBIUS-WEIGHTED POINT COUNT (Fu-Wan style):
        sum_{k in (Z/m)^*} |T_alpha^{(k)}|^2 = sum_{d | m} d mu(m/d) N_d(alpha),
        N_d(alpha) = #{(t,s) in C_alpha^2, t,s != 1 : (1-t)/(1-s) in (F_q^*)^d}.
      This is the exact-integer mechanism behind the m=9 observation.

 (I4) VARIETY FORM (direct enumeration, small p): m^2 d N_d(alpha) =
        #{(x,y,z) in (F_q^*)^3 : 1 - g^alpha x^m = (1 - g^alpha y^m) z^d,
                                  both sides != 0}.

 (M)  MECHANISM: Weil main terms of (I3) cancel: sum_{d|m} d mu(m/d) |C|^2/d
      = |C|^2 sum_{d|m} mu(m/d) = 0 for m > 1 -- averaged mode energy is PURE
      error term; no direct polynomial(q) main term survives.

 (C)  CALIBRATION at m = 12 (FIRST OPEN instance): C_D(12) = E/(m^3 q^3) per
      character and Galois-averaged; integrality of the averaged energy;
      flatness constant sup_a |S(a)|^2/(m q).
"""

import cmath, math, sys

def primitive_root(p):
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
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise ValueError

def divisors(m):
    return [d for d in range(1, m + 1) if m % d == 0]

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

def build_ind(p, g):
    ind = {}
    x = 1
    for k in range(p - 1):
        ind[x] = k
        x = (x * g) % p
    return ind

def jacobi_ladder(p, m, k, ind):
    """J_j = J(lambda^j, lambda^k) for j in Z/m (lambda(t)=zeta_m^{ind t})."""
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    J = []
    for j in range(m):
        s = 0j
        for t in range(2, p):  # t != 0,1 ; t=1 gives chi(0)=0 anyway; skip t=1
            s += zm[(j * ind[t]) % m] * zm[(k * ind[(1 - t) % p]) % m]
        J.append(s)
    return J

def dist_energy_direct(J, m, u):
    D = [0j] * m
    for j1 in range(1, m):
        for j2 in range(1, m):
            for j3 in range(1, m):
                l1, l2, l3 = j1 % u, j2 % u, j3 % u
                if l1 != l2 and l1 != l3 and l2 != l3:
                    D[(j1 + j2 + j3) % m] += J[j1] * J[j2] * J[j3]
    return sum(abs(x) ** 2 for x in D), D

def spectral_energy(J, m, u):
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    E = 0.0
    Slist = []
    for a in range(m):
        A = [0j] * u
        for j in range(1, m):
            A[j % u] += zm[(a * j) % m] * J[j]
        S = sum(A)
        P2 = sum(x * x for x in A)
        P3 = sum(x ** 3 for x in A)
        Dh = S ** 3 - 3 * S * P2 + 2 * P3
        E += abs(Dh) ** 2
        Slist.append(S)
    return E / m, Slist

def T_alpha(p, m, k, ind, alpha):
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    s = 0j
    for t in range(2, p):
        if ind[t] % m == alpha % m:
            s += zm[(k * ind[(1 - t) % p]) % m]
    return s

def run_instance(p, m, verbose_variety=False):
    u = m // 3
    g = primitive_root(p)
    ind = build_ind(p, g)
    ks = [k for k in range(1, m) if math.gcd(k, m) == 1]
    q3 = float(p) ** 3

    res = {"p": p, "ok_I1": True, "ok_I2": True, "ok_I3": True, "ok_I4": True}
    Es, sups = [], []
    Tsq_by_alpha = [0.0] * m  # sum_k |T_alpha^(k)|^2 accumulated
    for k in ks:
        J = jacobi_ladder(p, m, k, ind)
        E_dir, _ = dist_energy_direct(J, m, u)
        E_spec, Slist = spectral_energy(J, m, u)
        if abs(E_dir - E_spec) > 1e-6 * max(1.0, E_dir):
            res["ok_I1"] = False
        # (I2): S(a) = m*T_{-a} + 1
        for a in range(m):
            T = T_alpha(p, m, k, ind, (-a) % m)
            if abs(Slist[a] - (m * T + 1)) > 1e-6 * max(1.0, abs(Slist[a])):
                res["ok_I2"] = False
            Tsq_by_alpha[(-a) % m] += abs(T) ** 2
        Es.append(E_dir)
        sups.append(max(abs(S) ** 2 for S in Slist) / (m * p))

    # (I3): Mobius point-count identity for each alpha
    for alpha in range(m):
        C = [t for t in range(2, p) if ind[t] % m == alpha]
        rhs = 0
        for d in divisors(m):
            mu = mobius(m // d)
            if mu == 0:
                continue
            Nd = 0
            for t in C:
                it = ind[(1 - t) % p]
                for s in C:
                    if (it - ind[(1 - s) % p]) % d == 0:
                        Nd += 1
            rhs += d * mu * Nd
        if abs(Tsq_by_alpha[alpha] - rhs) > 1e-4 * max(1.0, abs(rhs)):
            res["ok_I3"] = False

    # (I4): variety form, direct (x,y,z) enumeration at small p, alpha = 0,1, d = 3
    if verbose_variety:
        for alpha in (0, 1):
            C = [t for t in range(2, p) if ind[t] % m == alpha]
            for d in (3, u):
                Nd = sum(1 for t in C for s in C
                         if (ind[(1 - t) % p] - ind[(1 - s) % p]) % d == 0)
                ga = pow(g, alpha, p)
                cnt = 0
                for x in range(1, p):
                    lhs = (1 - ga * pow(x, m, p)) % p
                    if lhs == 0:
                        continue
                    for y in range(1, p):
                        rhs_ = (1 - ga * pow(y, m, p)) % p
                        if rhs_ == 0:
                            continue
                        # z^d = lhs/rhs_ has d solutions iff ind of ratio == 0 mod d
                        ratio = (lhs * pow(rhs_, p - 2, p)) % p
                        if ind[ratio] % d == 0:
                            cnt += d
                # each valid (t,s): m choices of x, m of y, d of z
                if cnt != m * m * Nd * d:
                    res["ok_I4"] = False
                print(f"    (I4) p={p} alpha={alpha} d={d}: variety count {cnt} "
                      f"vs m^2*d*N_d = {m*m*d*Nd}  {'OK' if cnt==m*m*d*Nd else 'FAIL'}")

    E_avg = sum(Es) / len(ks)
    res["E_avg"] = E_avg
    res["E_avg_int_dist"] = abs(E_avg * len(ks) - round(E_avg * len(ks)))
    res["C_per_char_max"] = max(Es) / (m ** 3 * q3)
    res["C_avg"] = E_avg / (m ** 3 * q3)
    res["flat_sup"] = max(sups)
    return res

def main():
    print(__doc__.splitlines()[1])
    for m, pmax, pvar in ((9, 1000, 40), (12, 1000, 40)):
        primes = [p for p in range(m + 1, pmax)
                  if p % m == 1 and all(p % r for r in range(2, int(math.isqrt(p)) + 1))]
        print(f"\n===== m = {m} (u' = {m//3}) : {len(primes)} primes p == 1 mod {m} =====")
        print(f"{'p':>5} {'I1':>3} {'I2':>3} {'I3':>3} {'phi*E_avg int?':>14} "
              f"{'C_max/char':>10} {'C_avg':>8} {'sup|S|^2/(mq)':>13}")
        allok = True
        maxC, maxflat = 0.0, 0.0
        for p in primes:
            r = run_instance(p, m, verbose_variety=(p < pvar))
            ok = r["ok_I1"] and r["ok_I2"] and r["ok_I3"] and r["ok_I4"]
            allok = allok and ok
            maxC = max(maxC, r["C_avg"])
            maxflat = max(maxflat, r["flat_sup"])
            print(f"{p:>5} {str(r['ok_I1'])[0]:>3} {str(r['ok_I2'])[0]:>3} "
                  f"{str(r['ok_I3'])[0]:>3} {r['E_avg_int_dist']:>14.6f} "
                  f"{r['C_per_char_max']:>10.4f} {r['C_avg']:>8.4f} {r['flat_sup']:>13.3f}")
        # Weil main-term cancellation (mechanism, exact arithmetic)
        mt = sum(d * mobius(m // d) for d in divisors(m))
        print(f"  mechanism: sum_d d*mu(m/d)*|C|^2/d main terms -> coeff "
              f"sum_(d|m) mu(m/d) = {sum(mobius(m//d) for d in divisors(m))} (=0 iff m>1: PURE ERROR TERM)")
        print(f"  m={m}: identities {'ALL VERIFIED' if allok else 'FAILURE'}; "
              f"C_avg sup = {maxC:.4f}; flatness sup|S|^2/(mq) = {maxflat:.3f}")
        if not allok:
            sys.exit(1)

if __name__ == "__main__":
    main()
