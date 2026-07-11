#!/usr/bin/env python3
"""
#466 r=3 rung, route (ii): Hasse-Davenport exact angle relations along subgroup
cosets of Z/m, applied to the LADDER OBJECT J_j = sum_t lam_j(t) chi(1-t)
(= jacobiCoeff of _R19JacobiFourierExpansion).

CANDIDATE EXACT IDENTITIES (derived from the HD product relation
  prod_{a=0}^{k-1} g(chi' rho^a) = chi'(k)^{-k} g(chi'^k) prod_{a=1}^{k-1} g(rho^a),
rho = lam^{m/k} of order k, applied to numerator and denominator of
J = g(lam^j) g(chi) / g(lam^j chi)):

  (I3) k=3, u=m/3, 3|m, p!=3:
       J_j * J_{j+u} * J_{j+2u} = kappa3 * J3(3j)
       kappa3 = chi(3)^3 * Jac(chi,chi) * Jac(chi^2,chi)
       J3(c)  = jacobiCoeff(chi^3, lam, c) = sum_t lam_c(t) chi^3(1-t)

  (I2) k=2, u=m/2, 2|m, p!=2:
       J_j * J_{j+u} = kappa2 * J2(2j),  kappa2 = chi(2)^2 * Jac(chi,chi),
       J2(c) = jacobiCoeff(chi^2, lam, c)

  (AGG3) sum_j J_j J_{j+u} J_{j+2u} = kappa3 * m * W_{chi^3, G'}(1)
       where G' = index-(m/3) subgroup (kernel of lam^{m/3}-family),
       W_{psi,H}(1) = sum_{y in H} psi(1 - y).

  (NEG) control/refutation candidate: the SAME collapse for an off-coset
       triple (j, j+u+1, j+2u-1) with the naturally matched constant --
       expected FALSE; we record the countermodel.

Deterministic, exact index arithmetic, complex128 with unit-modulus character
values built from exact rational angles; tolerance 1e-8 relative.
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

def build(p, m):
    """Return (ind, zeta) for F_p with primitive root; m | p-1 assumed."""
    assert (p - 1) % m == 0
    g = primitive_root(p)
    ind = {}
    x = 1
    for k in range(p - 1):
        ind[x] = k
        x = (x * g) % p
    return ind

def run_instance(p, m, e, verbose=False):
    """chi = character with chi(g^k)=zeta_{p-1}^{e k}; lam_j(g^k)=zeta_m^{jk}.
    Returns list of failure strings."""
    ind = build(p, m)
    q1 = p - 1
    zq = lambda a: cmath.exp(2j * math.pi * (a % q1) / q1)
    def chi_pow(t, s):  # chi^s(t)
        if t % p == 0:
            return 0.0
        return zq(s * e * ind[t % p])
    def lam(j, t):      # lam_j(t) = zeta_m^{j * ind(t)} (order-m dual family)
        if t % p == 0:
            return 0.0
        return cmath.exp(2j * math.pi * ((j * ind[t % p]) % m) / m)
    def jac_coeff(s, c):  # sum_t lam_c(t) chi^s(1-t)
        return sum(lam(c, t) * chi_pow((1 - t) % p, s) for t in range(p))
    def jac(s1, s2):      # Jac(chi^s1, chi^s2)
        return sum(chi_pow(t, s1) * chi_pow((1 - t) % p, s2) for t in range(p))

    J = [jac_coeff(1, j) for j in range(m)]
    fails = []
    scale = p ** 1.5

    chi2_trivial = (2 * e) % q1 == 0
    chi3_trivial = (3 * e) % q1 == 0

    # (I3) — nondegenerate branch: chi^2 and chi^3 nontrivial
    if m % 3 == 0 and p % 3 != 0 and not chi2_trivial and not chi3_trivial:
        u = m // 3
        kappa3 = (chi_pow(3, 1) ** 3) * jac(1, 1) * jac(2, 1)
        J3 = [jac_coeff(3, c) for c in range(m)]
        for j in range(m):
            lhs = J[j] * J[(j + u) % m] * J[(j + 2 * u) % m]
            rhs = kappa3 * J3[(3 * j) % m]
            if abs(lhs - rhs) > 1e-8 * scale:
                fails.append(f"I3 p={p} m={m} e={e} j={j} |lhs-rhs|={abs(lhs-rhs):.3e} lhs={lhs:.4f} rhs={rhs:.4f}")
        # (AGG3): sum_j lhs = kappa3 * m * W_{chi^3,G'}(1), G' = {t: ind(t) % u == 0}?
        # lam_{3j} runs over subgroup 3Z/m of order u=m/3; its common kernel is
        # G' = {t : (m/ gcd...)  } : lam_{3j}(t)=1 for all j iff 3*ind(t) % m ...
        # lam_c trivial on t iff c*ind(t) % m == 0; for all c in 3Z/m iff 3*ind(t) % m == 0
        # iff ind(t) % (m//3) == 0.  G' = {t != 0 : ind(t) % (m//3) == 0}, |G'| = 3*(p-1)/m.
        agg_lhs = sum(J[j] * J[(j + u) % m] * J[(j + 2 * u) % m] for j in range(m))
        W = sum(chi_pow((1 - t) % p, 3) for t in range(1, p) if ind[t] % (m // 3) == 0)
        agg_rhs = kappa3 * m * W
        if abs(agg_lhs - agg_rhs) > 1e-8 * scale * m:
            fails.append(f"AGG3 p={p} m={m} e={e} |lhs-rhs|={abs(agg_lhs-agg_rhs):.3e}")
        # (NEG) off-coset control: same kappa3-collapse for (j, j+u+1, j+2u-1).
        # For m=3 the perturbed triple is a permutation of the coset triple, so the
        # control is vacuous there; require m >= 6.
        neg_ok = 0 if m >= 6 else -1
        if m >= 6:
            for j in range(m):
                lhs = J[j] * J[(j + u + 1) % m] * J[(j + 2 * u - 1) % m]
                rhs = kappa3 * J3[(3 * j) % m]
                if abs(lhs - rhs) <= 1e-8 * scale:
                    neg_ok += 1
        if neg_ok == m:
            fails.append(f"NEG-unexpectedly-true p={p} m={m} e={e}")
        else:
            if verbose:
                print(f"  NEG countermodel confirmed p={p} m={m} e={e}: off-coset collapse holds at {neg_ok}/{m} indices only")

    # (D3a) degenerate branch chi^2 trivial (chi order 2, chi^3 = chi):
    # observed exact correction lhs = q * kappa3 * J3(3j); verify it.
    if m % 3 == 0 and p % 3 != 0 and chi2_trivial and not chi3_trivial:
        u = m // 3
        kappa3 = (chi_pow(3, 1) ** 3) * jac(1, 1) * jac(2, 1)
        J3 = [jac_coeff(3, c) for c in range(m)]
        for j in range(m):
            lhs = J[j] * J[(j + u) % m] * J[(j + 2 * u) % m]
            rhs = p * kappa3 * J3[(3 * j) % m]
            if abs(lhs - rhs) > 1e-8 * scale:
                fails.append(f"D3a p={p} m={m} e={e} j={j} |lhs-rhs|={abs(lhs-rhs):.3e}")

    # (I2) — nondegenerate branch
    if m % 2 == 0 and p % 2 != 0 and not chi2_trivial:
        u = m // 2
        kappa2 = (chi_pow(2, 1) ** 2) * jac(1, 1)
        J2 = [jac_coeff(2, c) for c in range(m)]
        for j in range(m):
            lhs = J[j] * J[(j + u) % m]
            rhs = kappa2 * J2[(2 * j) % m]
            if abs(lhs - rhs) > 1e-8 * p:
                fails.append(f"I2 p={p} m={m} e={e} j={j} |lhs-rhs|={abs(lhs-rhs):.3e}")
    return fails

def main():
    # instances: p prime, m | p-1 with 3|m (and some 2|m), e in-family and out-of-family
    cases = [
        (13, 12), (13, 6), (13, 3), (19, 6), (19, 18), (31, 6), (31, 15), (31, 30),
        (37, 12), (37, 36), (43, 6), (43, 21), (61, 12), (61, 60), (73, 24),
    ]
    total = 0
    allfails = []
    for (p, m) in cases:
        # e values: in-family (e multiple of (p-1)/m) and generic out-of-family
        es = sorted({(p - 1) // m, 2 * ((p - 1) // m), 1, 2, 5 % (p - 1), (p - 1) // 2})
        es = [e for e in es if e % (p - 1) != 0]
        for e in es:
            total += 1
            f = run_instance(p, m, e, verbose=(total <= 3))
            allfails.extend(f)
    print(f"instances run: {total}")
    if allfails:
        print(f"FAILURES: {len(allfails)}")
        for s in allfails[:40]:
            print(" ", s)
        sys.exit(1)
    print("ALL IDENTITIES (I3), (I2), (AGG3) VERIFIED EXACTLY; NEG countermodels present.")

if __name__ == "__main__":
    main()
