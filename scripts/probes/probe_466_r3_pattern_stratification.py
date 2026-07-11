#!/usr/bin/env python3
"""
#466 r=3: pattern stratification of the off-coset remainder R.

(a) Partition ordered nonzero triples (j1,j2,j3), j1+j2+j3=d, by the multiset of
    H-cosets (H = {0,u,2u}, u=m/3; coset index = j mod u):
      FULL  = same coset, within-coset offsets a permutation of (0,u,2u)  [= A, extracted]
      SAME3 = same coset, not full-covering (repeated offsets)
      TWO   = exactly two indices in one coset
      DIST  = all three in distinct cosets
    Report per-pattern energies E_P = sum_d |T_P(d)|^2 vs wick = 6 m^3 q^3.

(b) (I2)-driven collapse of the m/2-pair stratum (needs 2|m):  with v = m/2,
      S(d) := sum_{j!=0, j+v!=0, k:=d-2j-v!=0} J_j J_{j+v} J_k
    candidate (HP1):  S(d) = kappa2 * M(d),
      M(d) := sum_{same index conditions} J2(2j) * J_k,   kappa2 = chi(2)^2 Jac(chi,chi)
    (per-pair exact by (I2) => should hold; verify).  Calibrate the mixed-conv
    energy sum_d |M(d)|^2 / (m^2 q^2)  (r=2-type Wick scale).

(c) Square-root-cancellation growth check on the dominant pattern: fixed m,
    growing p: report E_DIST/wick (flat O(1) = square-root cancellation present).

Deterministic exact index arithmetic, complex128.
"""

import cmath, math, sys
from probe_466_r3_hasse_davenport_coset import primitive_root, build

def run_instance(p, m, e):
    ind = build(p, m)
    q1 = p - 1
    zq = lambda a: cmath.exp(2j * math.pi * (a % q1) / q1)
    def chi_pow(t, s):
        return 0.0 if t % p == 0 else zq(s * e * ind[t % p])
    def lam(j, t):
        return 0.0 if t % p == 0 else cmath.exp(2j * math.pi * ((j * ind[t % p]) % m) / m)
    def jac_coeff(s, c):
        return sum(lam(c, t) * chi_pow((1 - t) % p, s) for t in range(p))
    def jac(s1, s2):
        return sum(chi_pow(t, s1) * chi_pow((1 - t) % p, s2) for t in range(p))

    J = [jac_coeff(1, j) for j in range(m)]
    u = m // 3
    wick = 6 * (m ** 3) * (p ** 3)
    fails = []

    # (a) pattern partition
    T = {pat: [0j] * m for pat in ("FULL", "SAME3", "TWO", "DIST")}
    for j1 in range(1, m):
        for j2 in range(1, m):
            for j3 in range(1, m):
                d = (j1 + j2 + j3) % m
                v = J[j1] * J[j2] * J[j3]
                c1, c2, c3 = j1 % u, j2 % u, j3 % u
                ncos = len({c1, c2, c3})
                if ncos == 3:
                    pat = "DIST"
                elif ncos == 2:
                    pat = "TWO"
                else:  # same coset
                    if len({j1, j2, j3}) == 3:
                        pat = "FULL"
                    else:
                        pat = "SAME3"
                T[pat][d] += v
    E = {pat: sum(abs(x) ** 2 for x in T[pat]) for pat in T}
    tc_energy = sum(abs(sum(T[pat][d] for pat in T)) ** 2 for d in range(m))

    # (b) m/2-pair stratum, if 2|m and chi^2 nontrivial
    hp = None
    if m % 2 == 0 and (2 * e) % q1 != 0:
        v = m // 2
        kappa2 = (chi_pow(2, 1) ** 2) * jac(1, 1)
        J2 = [jac_coeff(2, c) for c in range(m)]
        S = [0j] * m
        M = [0j] * m
        for j in range(m):
            if j % m == 0 or (j + v) % m == 0:
                continue
            for d in range(m):
                k = (d - 2 * j - v) % m
                if k == 0:
                    continue
                S[d] += J[j] * J[(j + v) % m] * J[k]
                M[d] += J2[(2 * j) % m] * J[k]
        for d in range(m):
            if abs(S[d] - kappa2 * M[d]) > 1e-8 * p ** 3:
                fails.append(f"HP1 p={p} m={m} e={e} d={d} |diff|={abs(S[d]-kappa2*M[d]):.3e}")
        ES = sum(abs(x) ** 2 for x in S)
        EM = sum(abs(x) ** 2 for x in M)
        hp = (ES / wick, EM / (m ** 2 * p ** 2))
    return fails, {pat: E[pat] / wick for pat in E}, tc_energy / wick, hp

def main():
    print("(a)+(b): per-pattern energies / wick, and (I2) half-pair stratum")
    print(f"{'p':>4} {'m':>3} {'e':>3} {'FULL':>8} {'SAME3':>8} {'TWO':>8} {'DIST':>8} {'total':>8} {'E_S/wick':>9} {'E_M/(m2q2)':>10}")
    cases = [(13, 12, 1), (13, 12, 5), (13, 6, 1), (19, 6, 1), (19, 18, 1),
             (31, 6, 1), (31, 15, 1), (31, 30, 1), (37, 12, 1), (37, 36, 5),
             (43, 21, 2), (61, 12, 1), (73, 24, 1), (73, 24, 5)]
    allfails = []
    for (p, m, e) in cases:
        q1 = p - 1
        if (2 * e) % q1 == 0 or (3 * e) % q1 == 0:
            continue
        fails, Ep, tot, hp = run_instance(p, m, e)
        allfails.extend(fails)
        hps = f"{hp[0]:>9.4f} {hp[1]:>10.4f}" if hp else f"{'--':>9} {'--':>10}"
        print(f"{p:>4} {m:>3} {e:>3} {Ep['FULL']:>8.4f} {Ep['SAME3']:>8.4f} {Ep['TWO']:>8.4f} {Ep['DIST']:>8.4f} {tot:>8.4f} {hps}")

    print("\n(c): growth check, fixed m=12, growing p (DIST/wick flat = sqrt-cancellation)")
    print(f"{'p':>4} {'DIST/wick':>10} {'TWO/wick':>9} {'total/wick':>10}")
    for p in (13, 37, 61, 73, 97, 109, 157, 181):
        fails, Ep, tot, hp = run_instance(p, 12, 1)
        allfails.extend(fails)
        print(f"{p:>4} {Ep['DIST']:>10.4f} {Ep['TWO']:>9.4f} {tot:>10.4f}")

    print(f"\nstructural failures (HP1): {len(allfails)}")
    for s in allfails[:20]:
        print(" ", s)
    if allfails:
        sys.exit(1)
    print("HP1 ((I2) half-pair stratum collapse to kappa2*(J2*J) mixed conv) EXACT everywhere tested.")

if __name__ == "__main__":
    main()
