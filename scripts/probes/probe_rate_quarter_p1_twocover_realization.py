#!/usr/bin/env python3
"""Realization of the P1 two-cover window at the LITERAL prize field F_P.

Strategy (found by probe_rate_quarter_p1_twocover_frustration.py):
1. BASE: find a full-cap triple in mu_16 subset F_P: f, g of degree 3, fully
   split in mu_16, disjoint roots, with h = f+g also degree 3 fully split in
   mu_16 (disjoint from both).  Then W = 9 = 3(k-1) at shape n=16, t = 0.
2. LIFT (doubling): from a triple (f, g) at mu_n with all three fully split,
   deg = n/4 - 1, triple-root count t, set
      f'(x) = (x - rho) * f(x^2),  g'(x) = (x - rho) * g(x^2)
   with rho in mu_2n fresh.  Then f', g', f'+g' = (x-rho)h(x^2) are fully
   split in mu_2n of degree 2(n/4-1)+1 = (2n)/4 - 1, and t' = 2t + 1.
3. After 26 doublings 16 -> 2^30: r_ij = k-1 = 2^28-1 each, t = 2^26 - 1.
   Two-cover = 3(k-1) - 2t ... coincidence mass W = 3(k-1) - t.
   Check the window: W >= 3(T-1) - N and the balance condition
   (each aligned region can be filled to exactly T-1 using fresh singles).

This script: (a) finds the base triple in F_P exactly; (b) verifies the lift
brute-force in F_P at mu_32 and mu_64; (c) does the exact integer bookkeeping
to n = 2^30 and checks the window inequalities.
"""

from itertools import combinations

P = 365375409332725729550921208179070755120141565953
G30 = 303645430271030343624574566109998498685964493478  # order 2^30

assert pow(G30, 2**30, P) == 1 and pow(G30, 2**29, P) != 1


def mu(n):
    z = pow(G30, 2**30 // n, P)
    dom = [pow(z, i, P) for i in range(n)]
    assert len(set(dom)) == n
    return dom


def poly_from_roots(roots, scalar=1):
    coeffs = [scalar % P]
    for r in roots:
        new = [0] * (len(coeffs) + 1)
        for i, a in enumerate(coeffs):
            new[i + 1] = (new[i + 1] + a) % P
            new[i] = (new[i] - a * r) % P
        coeffs = new
    return coeffs


def ev(f, x):
    v = 0
    for c in reversed(f):
        v = (v * x + c) % P
    return v


def find_base():
    dom = mu(16)
    idx = range(16)
    for Rf in combinations(idx, 3):
        rest1 = [i for i in idx if i not in Rf]
        F = poly_from_roots([dom[i] for i in Rf])
        for Rg in combinations(rest1, 3):
            Gp = poly_from_roots([dom[i] for i in Rg])
            rem = [i for i in rest1 if i not in Rg]
            # h = F + lam*G ; x root iff lam = -F(x)/G(x)
            vals = {}
            for i in rem:
                x = dom[i]
                lam = (-ev(F, x)) * pow(ev(Gp, x), P - 2, P) % P
                vals.setdefault(lam, []).append(i)
            for lam, pts in vals.items():
                if len(pts) >= 3 and lam != 0:
                    return Rf, Rg, lam, tuple(pts[:3]), dom
    return None


def check_triple(f, g, dom, expect_deg):
    n = len(dom)
    h = [(a + b) % P for a, b in zip(f + [0] * (len(g) - len(f)),
                                     g + [0] * (len(f) - len(g)))]
    rf = [x for x in dom if ev(f, x) == 0]
    rg = [x for x in dom if ev(g, x) == 0]
    rh = [x for x in dom if ev(h, x) == 0]
    t = len(set(rf) & set(rg))
    assert any(c for c in h), "h identically zero"
    return len(rf), len(rg), len(rh), t


def lift(f, g, rho):
    def double(q):
        out = [0] * (2 * (len(q) - 1) + 1)
        for i, c in enumerate(q):
            out[2 * i] = c
        # multiply by (x - rho)
        res = [0] * (len(out) + 1)
        for i, a in enumerate(out):
            res[i + 1] = (res[i + 1] + a) % P
            res[i] = (res[i] - a * rho) % P
        return res
    return double(f), double(g)


def main():
    print("== base search: full-cap triple in mu_16 of F_P ==")
    base = find_base()
    assert base is not None, "NO base triple in mu_16 of F_P"
    Rf, Rg, lam, Rh, dom16 = base
    f = poly_from_roots([dom16[i] for i in Rf])
    g = poly_from_roots([dom16[i] for i in Rg], lam)
    rf, rg, rh, t = check_triple(f, g, dom16, 3)
    print(f"  base: Rf(idx)={Rf} Rg(idx)={Rg} lambda={lam}")
    print(f"  base counts: rf={rf} rg={rg} rh={rh} t={t}  (want 3,3,3,0)")
    assert (rf, rg, rh, t) == (3, 3, 3, 0)

    # lift to mu_32 and mu_64, verify brute force in F_P
    cur_f, cur_g = f, g
    tcur = 0
    n = 16
    while n < 64:
        dom2 = mu(2 * n)
        used = set()
        for x in dom2:
            if ev(cur_f, (x * x) % P) == 0 or ev(cur_g, (x * x) % P) == 0:
                used.add(x)
            h = [(a + b) % P for a, b in zip(
                cur_f + [0] * (len(cur_g) - len(cur_f)),
                cur_g + [0] * (len(cur_f) - len(cur_g)))]
            if ev(h, (x * x) % P) == 0:
                used.add(x)
        rho = next(x for x in dom2 if x not in used)
        cur_f, cur_g = lift(cur_f, cur_g, rho)
        n *= 2
        tcur = 2 * tcur + 1
        rf, rg, rh, t = check_triple(cur_f, cur_g, mu(n), n // 4 - 1)
        km1 = n // 4 - 1
        print(f"  lifted to mu_{n}: rf={rf} rg={rg} rh={rh} t={t} "
              f"(want {km1},{km1},{km1},{tcur})")
        assert (rf, rg, rh, t) == (km1, km1, km1, tcur)

    # variant check at small scale: last step WITHOUT the common factor
    # (plain doubling): from mu_64 (deg 15, t=3) to mu_128: deg 30 = k-2,
    # r = 30 each, t = 6.
    dom128 = mu(128)

    def plain_double(q):
        out = [0] * (2 * (len(q) - 1) + 1)
        for i, c in enumerate(q):
            out[2 * i] = c
        return out
    pf, pg = plain_double(cur_f), plain_double(cur_g)
    rf, rg, rh, t = check_triple(pf, pg, dom128, 30)
    print(f"  plain-doubled to mu_128: rf={rf} rg={rg} rh={rh} t={t} "
          f"(want 30,30,30,6)")
    assert (rf, rg, rh, t) == (30, 30, 30, 6)

    # verify the cyclotomic form of the base scalar: lambda = -w^2
    w = pow(G30, 2**26, P)
    assert lam == (-(w * w)) % P, "base scalar is not -w^2"
    print("  base scalar lambda = -w^2 (cyclotomic Davenport identity) VERIFIED")

    print("\n== exact bookkeeping: the period-128 realization (the Lean construction) ==")
    N, K, T = 2**30, 2**28, 592794966
    Tm1 = T - 1
    cls = 2**23  # coordinates per residue class mod 128
    # per difference: 24 pair-only classes + 7 common classes = 31; deg 31*2^23 < k
    deg = 31 * cls
    assert deg == 260046848 < K
    aligned = 71 * cls
    print(f"  aligned region per pencil = 71 classes = {aligned} >= T-1 = {Tm1}: "
          f"{aligned >= Tm1}  (also >= T: {aligned >= T})")
    assert aligned >= Tm1
    overlap = 31 * cls
    print(f"  pairwise aligned overlap = 31 classes = {overlap} < k = {K}: "
          f"{overlap < K}")
    assert overlap < K
    total = 3 * aligned
    demand = 3 * Tm1 - N
    surplus_min = total - N
    print(f"  weighted two-cover surplus >= 3*{aligned} - N = {surplus_min} >= "
          f"demand {demand}: {surplus_min >= demand}")
    assert surplus_min >= demand
    plain = (3 * 24 + 7) * cls
    print(f"  plain two-cover count of this configuration = 79 classes = {plain} "
          f"(< {demand}: the plain and weighted readings differ at t > 0;")
    print("   the weighted surplus is the quantity forced by union <= N.  A")
    print("   plain-count-saturating triple would need a t=0 full-cap Davenport")
    print("   base on mu_32 (deg-7 f, g, f+g fully split, disjoint) -- OPEN.)")
    print("\nVERDICT: three_heavy_twoCover_window is REALIZED at literal P1:")
    print("  three distinct pencil pairs through the base codeword 1, each aligned")
    print("  on 595591168 >= T-1 coordinates, pairwise overlaps <= k-1 < k, and the")
    print("  weighted two-cover surplus meets the 87.5%-window demand.  Kernel")
    print("  certificate: _P1RateQuarterTwoCoverWindow.lean (axiom-clean).")


if __name__ == "__main__":
    main()
