#!/usr/bin/env python3
"""G96 probe B: does ZZ[X]-realizability bite beyond the real-moment relaxation?

At small m: compute the TRUE period polynomial exactly (integer coefficients via exact
power sums from N0 counts), pin the head coefficients e_1..e_3 (= depth-3 data
P1=-1, P2=p-n, P3), and search monic ZZ[X] of degree m with that head, all real roots,
|roots| <= n, maximizing the house.  Compare: ZZ-max vs real-relaxation max vs true M.
Also: discriminant + Mahler measure of true poly and of the ZZ-escape witness.
"""
import numpy as np
from itertools import product
from fractions import Fraction
from probe_g96_extremal import period_values, primitive_root

def exact_power_sums(p, n, Rmax):
    """P_r for the distinct-value set, exactly, via N0(r) counts (integer DP mod p)."""
    g = primitive_root(p)
    m = (p-1)//n
    gm = pow(g, m, p)
    mun = sorted(set(pow(gm, k, p) for k in range(n)))
    assert len(mun) == n
    # DP: cnt[k] = #{r-tuples of mu_n summing to k mod p}; python ints (exact)
    P = {0: n}  # P_0 = m actually; handle separately
    cnt = [0]*p
    cnt[0] = 1
    Ps = [m]
    for r in range(1, Rmax+1):
        new = [0]*p
        for x in mun:
            for k in range(p):
                new[(k+x) % p] += cnt[k]
        cnt = new
        N0 = cnt[0]
        # n * P_r = p*N0(r) - n^r
        num = p*N0 - n**r
        assert num % n == 0, (p, n, r)
        Ps.append(num // n)
    return Ps, mun

def newton_e_from_P(Ps, m):
    """elementary symmetric e_1..e_m from power sums P_1..P_m (exact fractions)."""
    e = [Fraction(1)]  # e_0
    for k in range(1, m+1):
        s = Fraction(0)
        for i in range(1, k+1):
            s += (-1)**(i-1) * e[k-i] * Ps[i]
        e.append(s / k)
    return e

def poly_from_e(e, m):
    """monic coefficients [1, -e1, +e2, ...] highest first."""
    return [(-1)**k * e[k] for k in range(m+1)]

def all_real_roots_in(coeffs, n, tol=1e-8):
    r = np.roots([float(c) for c in coeffs])
    if np.abs(r.imag).max() > tol*max(1.0, np.abs(r).max()):
        return None
    rr = np.sort(r.real)
    if np.abs(rr).max() > n + 1e-9:
        return None
    return rr

def disc_and_mahler(roots, lead=1):
    m = len(roots)
    d = 1.0
    for i in range(m):
        for j in range(i+1, m):
            d *= (roots[i]-roots[j])**2
    mah = np.prod([max(1.0, abs(x)) for x in roots])
    return d, mah

def run_small(p, n):
    m = (p-1)//n
    Ps, mun = exact_power_sums(p, n, m)
    e = newton_e_from_P(Ps, m)
    ints = all(x.denominator == 1 for x in e[1:])
    coeffs_true = poly_from_e(e, m)
    print(f"\n### p={p} n={n} m={m}")
    print(f"exact P_1..P_{m} = {Ps[1:]}")
    print(f"period polynomial e_k integral: {ints}")
    print(f"true period poly coeffs (monic, high->low): {[int(c) for c in coeffs_true]}")
    vals = np.sort(period_values(p, n))
    M = np.abs(vals).max()
    dtrue, mahtrue = disc_and_mahler(vals)
    print(f"true roots: {np.round(vals,4)}  M={M:.4f}  disc={dtrue:.6g}  Mahler={mahtrue:.4f}")
    return Ps, e, coeffs_true, vals, M

def exhaustive_m5(p, n, e, M, relax3):
    """m=5: pin e1,e2,e3; scan integer (e4,e5); all-real roots in [-n,n]; max house."""
    m = 5
    e1, e2, e3 = int(e[1]), int(e[2]), int(e[3])
    best = None
    # bounds: |e4| <= C(5,4) n^4 loose; use root-structure-informed window around feasible
    E4 = 500; E5 = 900
    found = []
    for e4 in range(-E4, E4+1):
        for e5 in range(-E5, E5+1):
            coeffs = [1, -e1, e2, -e3, e4, -e5]
            rr = all_real_roots_in(coeffs, n)
            if rr is None:
                continue
            house = np.abs(rr).max()
            found.append((house, e4, e5, rr))
    found.sort(key=lambda t: -t[0])
    print(f"ZZ[X] all-real-rooted, |roots|<={n}, head pinned (e1,e2,e3)=({e1},{e2},{e3}): "
          f"{len(found)} polynomials found")
    for house, e4, e5, rr in found[:5]:
        d, mah = disc_and_mahler(rr)
        print(f"  house={house:.4f}  (e4,e5)=({e4},{e5})  roots={np.round(rr,3)}  "
              f"disc={d:.4g} Mahler={mah:.3f}")
    if found:
        h = found[0][0]
        print(f"ZZ-max house = {h:.4f}   real-relax depth-3 = {relax3:.4f}   true M = {M:.4f}   "
              f"ZZ-max/relax = {h/relax3:.4f}")
    return found

def relax_depth3(Ps, m, n):
    """real relaxation with P1,P2,P3 pinned: spike H (either sign) + bulk measure mass m-1
    on [-n,n]: odd-truncated Hankel feasibility, binary search."""
    P = [float(x) for x in Ps]
    def feas1(H):
        mu = [1.0]
        for r in range(1, 4):
            mu.append((P[r] - H**r)/((m-1)*n**r))
        # D=3, k=1: H_1 = [[mu0,mu1],[mu1,mu2]] psd; localizers [(1 -x) mu], [(1+x) mu] on [-1,1]
        H1 = np.array([[mu[0], mu[1]], [mu[1], mu[2]]])
        L1 = np.array([[mu[0]-mu[1], mu[1]-mu[2]], [mu[1]-mu[2], mu[2]-mu[3]]])
        L2 = np.array([[mu[0]+mu[1], mu[1]+mu[2]], [mu[1]+mu[2], mu[2]+mu[3]]])
        tol = 1e-11
        return all(np.linalg.eigvalsh(A).min() >= -tol*max(1e-30, np.abs(A).max())
                   for A in (H1, L1, L2))
    def feas(H): return feas1(H) or feas1(-H)
    lo, hi = 0.0, float(n)
    if feas(hi-1e-12): return hi
    for _ in range(60):
        mid = 0.5*(lo+hi)
        if feas(mid): lo = mid
        else: hi = mid
    return lo

def rounding_search(p, n, Dpin=3, tries=40000, seed=0):
    """larger m: sample near-escape root configurations, round tail coefficients to ZZ,
    keep all-real-rooted ones with pinned head; report best house."""
    rng = np.random.default_rng(seed)
    m = (p-1)//n
    Ps, _ = exact_power_sums(p, n, min(m, Dpin))
    # exact head e1..e3
    e = newton_e_from_P(Ps + [0]*(m-len(Ps)+1), Dpin)
    e1, e2, e3 = int(e[1]), int(e[2]), int(e[3])
    vals = np.sort(period_values(p, n))
    M = np.abs(vals).max()
    relax3 = relax_depth3(Ps + [0]*3, m, n)
    best = (0.0, None)
    P1, P2, P3 = float(Ps[1]), float(Ps[2]), float(Ps[3])
    for t in range(tries):
        # escape ansatz: spike at -H (sign matching P3<0 pressure), bulk random
        H = rng.uniform(0.85, 1.0)*relax3
        sgn = -1 if rng.random() < 0.7 else 1
        spike = sgn*H
        # bulk: m-1 values; start from true values shape, jitter
        bulk = rng.choice(vals.astype(np.float64), m-1, replace=True) + rng.normal(0, 0.6, m-1)
        # fix first three power sums exactly on the reals by affine+pair adjustments:
        v = np.concatenate([[spike], bulk]).astype(np.float64)
        # project: adjust 3 designated bulk coords by Newton iteration to match P1..P3
        idx = [1, 2, 3]
        for it in range(60):
            F = np.array([v.sum()-P1, (v**2).sum()-P2, (v**3).sum()-P3])
            if np.abs(F).max() < 1e-10: break
            J = np.array([[1.0]*3, [2*v[i] for i in idx], [3*v[i]**2 for i in idx]])
            try:
                dx = np.linalg.solve(J, F)
            except np.linalg.LinAlgError:
                break
            for kk, i in enumerate(idx): v[i] -= dx[kk]
        else:
            pass
        if np.abs(F).max() > 1e-8 or np.abs(v).max() > n:
            continue
        # coefficients; round tail to integers
        c = np.polynomial.polynomial.polyfromroots(v)[::-1]  # high->low, monic
        ci = np.round(c).astype(np.int64)
        ci[0] = 1
        ci[1], ci[2], ci[3] = -e1, e2, -e3
        rr = all_real_roots_in(list(ci), n)
        if rr is None:
            continue
        house = np.abs(rr).max()
        if house > best[0]:
            best = (house, ci.copy(), rr.copy())
    print(f"\n### rounding search p={p} n={n} m={m}: true M={M:.4f} relax3={relax3:.4f}")
    if best[1] is not None:
        print(f"best ZZ house = {best[0]:.4f}  ratio to relax3 = {best[0]/relax3:.4f}  "
              f"ratio to M = {best[0]/M:.4f}")
        print(f"coeffs: {list(best[1])}")
    else:
        print("no ZZ witness found")
    return best

if __name__ == "__main__":
    # exact + exhaustive at m=5
    Ps, e, ct, vals, M = run_small(41, 8)
    relax3 = relax_depth3([float(x) for x in Ps[:4]], 5, 8)
    print(f"real-relaxation max-house(depth 3) = {relax3:.4f}")
    exhaustive_m5(41, 8, e, M, relax3)
    # exact polys at m=9, 11 (integrality sanity + disc/Mahler) and rounding search
    run_small(73, 8)
    run_small(89, 8)
    rounding_search(73, 8)
    rounding_search(89, 8)
