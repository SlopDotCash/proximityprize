#!/usr/bin/env python3
"""RESL2 big-cell probe: n=8, m=16, m'=2/4 at p=65537 and p=786433 (regime cell).
Measures: C_R = S4res_away / (q*(M n q)^2), sup|Res|/sqrt(Mnq), L2 ratio,
and the L4-Minkowski composed rung ratio:
  (m^4 S2D)^{1/4} <= n q^{1/4} + S4main^{1/4} + S4res^{1/4}  vs  (m^4 3 q Sigma^2)^{1/4}.
"""
import numpy as np, math

def cell(p, n, m, d):
    # generator
    def order(a):
        o, x = 1, a
        while x != 1:
            x = x * a % p; o += 1
        return o
    fact = []
    t = p - 1
    for f in (2, 3, 5, 7, 11, 13):
        while t % f == 0:
            fact.append(f); t //= f
    if t > 1: fact.append(t)
    fs = set(fact)
    g = next(a for a in range(2, 200) if all(pow(a, (p-1)//f, p) != 1 for f in fs))
    # dlog table
    dlog = np.zeros(p, dtype=np.int64)
    x = 1
    for k in range(p - 1):
        dlog[x] = k
        x = x * g % p
    mprime = m // math.gcd(m, d)
    fine = list(range(1, m))
    coarse = [d * t % m for t in range(1, mprime)]
    Omega = [t for t in fine if t not in coarse]
    M = len(Omega)
    G = np.unique(np.array([pow(g, (p-1)//n * j, p) for j in range(n)], dtype=np.int64))
    assert len(G) == n
    q = p; sq = math.sqrt(q)

    s0 = np.arange(p, dtype=np.int64)
    # chi^t(a) = exp(2pi i t dlog[a]/m), 0 at a=0
    def chi_vals(t, a):  # a array
        v = np.exp(2j * np.pi * ((t * dlog[a]) % m) / m)
        v[a == 0] = 0
        return v
    T = {}
    for t in fine:
        acc = np.zeros(p, dtype=np.complex128)
        for xg in G:
            acc += chi_vals(t, (s0 - xg) % p)
        T[t] = acc
    # gauss sums
    a = np.arange(1, p, dtype=np.int64)
    psi = np.exp(2j * np.pi * a / p)
    gs = {t: np.sum(chi_vals(t, a) * psi) for t in fine}
    for t in fine:
        assert abs(abs(gs[t]) - sq) < 1e-6 * sq
    Res = sum(gs[t] * np.conj(T[t]) for t in Omega)
    Main = sum(gs[t] * np.conj(T[t]) for t in coarse)
    mask = np.ones(p, dtype=bool)
    mask[0] = False
    mask[G] = False
    L2 = float(np.sum(np.abs(Res) ** 2))
    L2b = M*q*(n*q - n*n) + M*(M-1)*q*n*(n-1)*sq
    sup = float(np.max(np.abs(Res[mask])))
    S4res = float(np.sum(np.abs(Res[mask]) ** 4))
    S4main = float(np.sum(np.abs(Main[mask]) ** 4))
    mI = -n + Main + Res
    S2D = float(np.sum(np.abs(mI[mask]) ** 4))  # = m^4 S_2^D
    # Sigma over H = index-m subgroup
    H = np.unique(np.array([pow(g, m * j, p) for j in range((p-1)//m)], dtype=np.int64))
    eta = np.zeros(len(H), dtype=np.complex128)
    for i, b in enumerate(H):
        eta[i] = np.sum(np.exp(2j * np.pi * ((b * G) % p) / p))
    Sigma = float(np.sum(np.abs(eta) ** 2))
    budget = m**4 * 3 * q * Sigma**2
    CR = S4res / (q * (M*n*q)**2)
    mink_lhs = n * q**0.25 + S4main**0.25 + S4res**0.25
    mink_rhs = budget**0.25
    print(f"p={p} m'={mprime} M={M}: regime 16m^2n^2/q = {16*m*m*n*n/q:.3f}  n^4/q={n**4/q:.3f}")
    print(f"  L2 ratio={L2/L2b:.3f}  sup/sqrt(Mnq)={sup/math.sqrt(M*n*q):.3f}  C_R={CR:.3f}")
    print(f"  m^4 S2D actual = {S2D:.4g}  budget = {budget:.4g}  ratio = {S2D/budget:.3f}")
    print(f"  Minkowski: n q^1/4 + S4main^1/4 + S4res^1/4 = {mink_lhs:.4g} "
          f"vs budget^1/4 = {mink_rhs:.4g}  ratio = {mink_lhs/mink_rhs:.3f}")
    print(f"  pieces^(1/4): nq^.25={n*q**0.25:.4g} main={S4main**0.25:.4g} res={S4res**0.25:.4g}")
    print(f"  Sigma = {Sigma:.4g}  (nq/m = {n*q/m:.4g})")
    # theoretical Minkowski with C_R=2, Weil Cw=6 main bound:
    mainb = (6 * (mprime-1)**4 * n*n * q**3) ** 0.25
    resb = (2 * M*M * n*n * q**3) ** 0.25
    print(f"  THEORY: nq^.25+mainb+resb = {n*q**0.25 + mainb + resb:.4g} vs {mink_rhs:.4g} "
          f"ratio = {(n*q**0.25+mainb+resb)/mink_rhs:.3f}")
    print()

cell(65537, 8, 16, 8)
cell(65537, 8, 16, 4)
cell(786433, 8, 16, 8)
