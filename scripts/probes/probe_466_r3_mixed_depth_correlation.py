#!/usr/bin/env python3
"""
#466 r=3 successor move: (I3) as a change of variables INSIDE the sextic energy.

Decompose the Lean tripleConv (nonzero-index convention of _R21/_R22/_R23:
  selfConv(c)  = sum_{j!=0, c-j!=0} J_j J_{c-j}
  tripleConv(d)= sum_{j!=0} selfConv(d-j) J_j
i.e. ordered triples (j1,j2,j3), all nonzero, j1+j2+j3 = d) by coset pattern
w.r.t. the order-3 subgroup H = {0, u, 2u}, u = m/3:

  A(d) := sub-sum over ordered triples that are a PERMUTATION OF A FULL COSET
          {j, j+u, j+2u} (all distinct);  R(d) := tripleConv(d) - A(d).

CANDIDATE IDENTITIES:
  (P1) A(d) = 2 * sum_{j : 3j = d, d != 0} J_j J_{j+u} J_{j+2u}
       (the fiber {j : 3j=d} IS the unique contributing coset; 6 orderings;
        d=0 vanishes because the only candidate coset is H which contains 0).
  (M1) under HD (I3):  A(d) = 6*kappa*J3(d) for d in 3Z/m minus {0}, A = 0 else.
  (M3) candidate mixed-depth orthogonality:  X := sum_d A(d)*conj(R(d)) = 0 ?
       (expected FALSE -> record countermodel + measured size of X).
  (E)  energy split: sum||tc||^2 = sum||A||^2 + 2Re X + sum||R||^2 (algebra,
       sanity) + report ratios vs Wick scales.

Deterministic, exact index arithmetic, complex128; tolerances relative.
"""

import cmath, math, sys
from probe_466_r3_hasse_davenport_coset import primitive_root, build

def run_instance(p, m, e):
    ind = build(p, m)
    q1 = p - 1
    zq = lambda a: cmath.exp(2j * math.pi * (a % q1) / q1)
    def chi_pow(t, s):
        if t % p == 0:
            return 0.0
        return zq(s * e * ind[t % p])
    def lam(j, t):
        if t % p == 0:
            return 0.0
        return cmath.exp(2j * math.pi * ((j * ind[t % p]) % m) / m)
    def jac_coeff(s, c):
        return sum(lam(c, t) * chi_pow((1 - t) % p, s) for t in range(p))
    def jac(s1, s2):
        return sum(chi_pow(t, s1) * chi_pow((1 - t) % p, s2) for t in range(p))

    J = [jac_coeff(1, j) for j in range(m)]
    J3 = [jac_coeff(3, c) for c in range(m)]
    u = m // 3
    kappa = (chi_pow(3, 1) ** 3) * jac(1, 1) * jac(2, 1)

    # tripleConv, Lean convention, by direct enumeration; and A by pattern
    tc = [0j] * m
    A = [0j] * m
    for j1 in range(1, m):
        for j2 in range(1, m):
            for j3 in range(1, m):
                d = (j1 + j2 + j3) % m
                v = J[j1] * J[j2] * J[j3]
                tc[d] += v
                if len({j1, j2, j3}) == 3 and {j1, j2, j3} == {j1, (j1 + u) % m, (j1 + 2 * u) % m}:
                    A[d] += v
    R = [tc[d] - A[d] for d in range(m)]

    scale = p ** 3
    fails = []

    # (P1): A(d) = 2 * sum_{3j=d mod m, d!=0} ctp(j)
    for d in range(m):
        s = 0j
        if d != 0:
            for j in range(m):
                if (3 * j) % m == d:
                    s += J[j] * J[(j + u) % m] * J[(j + 2 * u) % m]
        if abs(A[d] - 2 * s) > 1e-8 * scale:
            fails.append(f"P1 p={p} m={m} e={e} d={d} |diff|={abs(A[d]-2*s):.3e}")

    # (M1): A(d) = 6*kappa*J3(d) on 3Z/m minus 0, zero elsewhere
    im3 = {(3 * j) % m for j in range(m)}
    for d in range(m):
        rhs = 6 * kappa * J3[d] if (d in im3 and d != 0) else 0j
        if abs(A[d] - rhs) > 1e-8 * scale:
            fails.append(f"M1 p={p} m={m} e={e} d={d} |diff|={abs(A[d]-rhs):.3e}")

    # (M3): X = sum_d A conj(R)  -- exact zero?
    X = sum(A[d] * R[d].conjugate() for d in range(m))
    EA = sum(abs(A[d]) ** 2 for d in range(m))
    ER = sum(abs(R[d]) ** 2 for d in range(m))
    ET = sum(abs(tc[d]) ** 2 for d in range(m))
    # energy split sanity
    if abs(ET - (EA + 2 * X.real + ER)) > 1e-6 * max(ET, 1):
        fails.append(f"ESPLIT p={p} m={m} e={e}")
    m3_zero = abs(X) <= 1e-8 * scale
    corr = abs(X) / math.sqrt(EA * ER) if EA > 0 and ER > 0 else float('nan')
    wick = 6 * (m ** 3) * (p ** 3)
    return fails, m3_zero, corr, EA / (m * p ** 3), ER / wick, ET / wick, abs(X) / (m ** 2 * p ** 3)

def main():
    cases = [(13, 12, 1), (13, 12, 2), (13, 12, 5), (13, 6, 1), (13, 6, 5),
             (19, 6, 1), (19, 18, 1), (19, 18, 5), (31, 6, 1), (31, 15, 1),
             (31, 30, 1), (31, 30, 7), (37, 12, 1), (37, 36, 5), (43, 21, 2),
             (61, 12, 1), (73, 24, 1), (73, 24, 5)]
    allfails = []
    n_m3_zero = 0
    total = 0
    print(f"{'p':>4} {'m':>3} {'e':>3} {'X==0':>5} {'|corr|':>8} {'EA/(m q^3)':>11} {'ER/wick':>8} {'ET/wick':>8} {'|X|/(m^2 q^3)':>13}")
    for (p, m, e) in cases:
        q1 = p - 1
        if (2 * e) % q1 == 0 or (3 * e) % q1 == 0:
            continue  # degenerate chi branches, out of (I3) scope
        total += 1
        fails, m3z, corr, ea, er, et, xn = run_instance(p, m, e)
        allfails.extend(fails)
        n_m3_zero += m3z
        print(f"{p:>4} {m:>3} {e:>3} {str(m3z):>5} {corr:>8.4f} {ea:>11.4f} {er:>8.4f} {et:>8.4f} {xn:>13.5f}")
    print(f"\ninstances: {total}; structural failures (P1/M1/ESPLIT): {len(allfails)}")
    for s in allfails[:30]:
        print(" ", s)
    print(f"M3 (mixed-depth orthogonality X==0) holds in {n_m3_zero}/{total} instances")
    if allfails:
        sys.exit(1)

if __name__ == "__main__":
    main()
