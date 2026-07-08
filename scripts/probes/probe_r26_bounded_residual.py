#!/usr/bin/env python3
"""RESL2 lane probe (#466 round 26): bounded-residual subfamily gate.

Checks, exactly:
 (1) The NEW cross second-moment identity, for chi' != chi'' nontrivial:
       sum_{s0 in F} T_{chi'}(s0) * conj(T_{chi''}(s0))
         = J0(chi',chi'') * sum_{x!=y in G} (chi' * bar(chi''))(x-y)
     where J0 = sum_u chi'(u) * conj(chi''(u+1))  (= chi'(-1) J(chi', chi''^{-1})),
     |J0| = sqrt(q).  Hence |cross| <= n(n-1) sqrt(q); diagonal (x=y) term is 0.
 (2) The residual L2 bound:
       sum_{s0} |Res(s0)|^2 <= M*q*(n*q - n^2) / q ... exact expansion:
       sum|Res|^2 = sum_{c',c'' in Omega} g(c') conj g(c'') CROSS(c',c'')
       <= M*q*(nq - n^2) + M(M-1)*q*n(n-1)*sqrt(q)     [Res without 1/m factor]
 (3) The rung budget: does Main(Stepanov/Weil) + Res(L2 x sup) fire
       m^4 * S_2^D <= 27*(q n^4 + S4main + S4res) <= m^4 * 3 q Sigma^2 ?
     Computes ACTUAL S4res, the L2-x-sup bound, and the deficit factor.

T here is shiftedCharSum: T_chi(s0) = sum_{x in G} chi(s0 - x); chi(0)=0.
Res(s0) = sum_{chi' in chiFamily(chi) \ chiFamily(chi^d)} g(chi') * conj(T_{chi'}(s0)).
(m * I_H(s0) = -n + Main_Y(s0) + Res(s0), H = Gchi chi.)
"""
import cmath, math, sys

def run_cell(p, n, m, d, verbose=True):
    # find generator of F_p^*
    def is_gen(g):
        seen = set(); x = 1
        for _ in range(p-1):
            x = x*g % p
            if x in seen: return False
            seen.add(x)
        return len(seen) == p-1
    g = next(a for a in range(2, p) if is_gen(a))
    # discrete logs
    dlog = {}
    x = 1
    for k in range(p-1):
        dlog[x] = k
        x = x*g % p
    assert (p-1) % m == 0 and (p-1) % n == 0
    # chi of order m: chi(g^k) = e(k/m)
    def chi_pow(t):  # returns function a -> chi^t(a)
        def f(a):
            if a % p == 0: return 0j
            return cmath.exp(2j*math.pi * (t * dlog[a % p] % m) / m)
        return f
    # G = mu_n
    G = sorted({pow(g, (p-1)//n * j, p) for j in range(n)})
    assert len(G) == n
    q = p
    sq = math.sqrt(q)

    # chiFamily(chi) = {chi^t : t=1..m-1}; chiFamily(chi^d) = powers of chi^d
    mprime = m // math.gcd(m, d)
    fine = list(range(1, m))
    coarse = [d*t % m for t in range(1, mprime)]
    Omega = [t for t in fine if t not in coarse]
    M = len(Omega)
    assert M == (m-1) - (mprime-1)

    # T_{chi^t}(s0) for all t in fine, all s0
    T = {t: [sum(chi_pow(t)((s0 - x) % p) for x in G) for s0 in range(p)] for t in fine}

    # Gauss sums g(chi^t) with psi(a)=e(a/p)
    def gauss(t):
        c = chi_pow(t)
        return sum(c(a) * cmath.exp(2j*math.pi*a/p) for a in range(1, p))
    gs = {t: gauss(t) for t in fine}
    for t in fine:
        assert abs(abs(gs[t]) - sq) < 1e-6 * sq

    # ---- (1) cross identity, few pairs
    errs = []
    for (t1, t2) in [(Omega[0], Omega[-1]), (Omega[0], Omega[1] if M > 1 else Omega[0])]:
        if t1 == t2: continue
        cross = sum(T[t1][s] * T[t2][s].conjugate() for s in range(p))
        c1, c2 = chi_pow(t1), chi_pow(t2)
        J0 = sum(c1(u) * c2((u+1) % p).conjugate() for u in range(1, p))
        lam = lambda a: c1(a) * c2(a).conjugate()
        S = sum(lam((x - y) % p) for x in G for y in G if x != y)
        errs.append(abs(cross - J0 * S))
        assert abs(abs(J0) - sq) < 1e-6 * sq, (t1, t2, abs(J0), sq)
        assert abs(cross) <= n*(n-1)*sq + 1e-6
    if verbose:
        print(f"p={p} n={n} m={m} d={d} m'={mprime} M={M}: cross identity max err = {max(errs):.2e}")

    # ---- (2) residual L2
    Res = [sum(gs[t] * T[t][s].conjugate() for t in Omega) for s in range(p)]
    L2 = sum(abs(r)**2 for r in Res)
    L2bound = M*q*(n*q - n*n) + M*(M-1)*q*n*(n-1)*sq
    if verbose:
        print(f"  L2(Res) actual = {L2:.4g}   bound = {L2bound:.4g}   ratio = {L2/L2bound:.3f}")
    assert L2 <= L2bound * (1 + 1e-9)

    # ---- (3) rung budget
    D = set(G) | {0}
    sup = max(abs(Res[s]) for s in range(p) if s not in D)
    supTriv = M * sq * n
    S4res = sum(abs(Res[s])**4 for s in range(p) if s not in D)
    S4res_l2sup = supTriv**2 * L2bound
    # Sigma for H = Gchi = {b: chi(b)=1} = index-m subgroup (m | p-1)
    H = sorted({pow(g, m*j, p) for j in range((p-1)//m)})
    eta = {b: sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in G) for b in H}
    Sigma = sum(abs(eta[b])**2 for b in H)
    wick = 3 * q * Sigma**2           # target for S_2^D
    m4wick = m**4 * wick              # budget for m^4 S_2^D
    # actual m^4 S_2^D
    I = {s: sum(eta[b].conjugate() * cmath.exp(2j*math.pi*(b*s % p)/p) for b in H)
         for s in range(p) if s not in D}
    S2D = sum(abs(v)**4 for v in I.values())
    # composed bound pieces (27-split): 27*(q n^4 + S4main + S4res)
    Main = {s: sum(gs[t] * T[t][s].conjugate() for t in coarse) for s in range(p) if s not in D}
    S4main = sum(abs(v)**4 for v in Main.values())
    lhs_actual = m**4 * S2D
    if verbose:
        print(f"  sup|Res| off D = {sup:.4g}  trivial sup bound = {supTriv:.4g}  "
              f"(sup/sqrt(Mnq) = {sup/math.sqrt(M*n*q):.3f})")
        print(f"  S4res actual   = {S4res:.4g}")
        print(f"  S4res L2xsup   = {S4res_l2sup:.4g}   overshoot = {S4res_l2sup/S4res:.3g}x")
        print(f"  S4res 'Wick'   = {3*q*(M*n*q)**2:.4g} (3q(Mnq)^2)  actual/wick = {S4res/(3*q*(M*n*q)**2):.3f}")
        print(f"  m^4 S_2^D act  = {lhs_actual:.4g}   m^4*3q*Sigma^2 = {m4wick:.4g}  "
              f"ratio = {lhs_actual/m4wick:.3g}")
        comp = 27*(q*n**4 + S4main + S4res_l2sup)
        print(f"  composed 27-split bound (with L2xsup) = {comp:.4g}  vs budget {m4wick:.4g}  "
              f"DEFICIT = {comp/m4wick:.3g}x")
        comp_act = 27*(q*n**4 + S4main + S4res)
        print(f"  composed 27-split with ACTUAL S4res   = {comp_act:.4g}  DEFICIT = {comp_act/m4wick:.3g}x")
        # needed strength: S4res <= m^4 wick/27 - qn^4 - S4main
        room = m4wick/27 - q*n**4 - S4main
        print(f"  room for S4res = {room:.4g}  -> need S4res <= room: "
              f"{'YES fires' if S4res <= room else 'NO'} (actual), "
              f"{'YES fires' if S4res_l2sup <= room else 'NO'} (L2xsup)")
    return dict(p=p, n=n, m=m, mprime=mprime, M=M, L2=L2, L2bound=L2bound, sup=sup,
                S4res=S4res, S4res_l2sup=S4res_l2sup, S2D=S2D, S4main=S4main,
                Sigma=Sigma, m4wick=m4wick)

if __name__ == "__main__":
    # exact small cells
    run_cell(p=97, n=8, m=16, d=8)   # m'=2
    print()
    run_cell(p=97, n=8, m=16, d=4)   # m'=4
    print()
    run_cell(p=193, n=8, m=16, d=8)
    print()
    run_cell(p=257, n=8, m=16, d=4)
