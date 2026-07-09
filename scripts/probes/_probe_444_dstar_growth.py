# _probe_444_dstar_growth.py  (#444 D*-growth-law attack)
#
# GOAL: pin the p-INDEPENDENT distinct-gamma count D*(n,r) = worst-over-line #bad-scalar,
# verify the two structural identities the campaign relies on, and measure the GROWTH LAW
# vs the budget n through the window.
#
# Object (deep band, deficit-2, m=1 rate family; k=r-1, a=r+1):
#   S = (r+1)-subset of mu_n is BAD for line (x^e, x^f)  <=>
#       h_{e-r}(S) h_{f-r+1}(S) = h_{f-r}(S) h_{e-r+1}(S)      [Schur-ratio variety V]
#   pinned bad scalar  gamma = - h_{e-r}(S) / h_{f-r}(S).
#
# IDENTITY CLAIMS to verify (from CONJ.md / DemandFloorReduction):
#   (I1)  gamma = -e_1(S)   on the deepest resonance? -> CHECK exactly (claimed "all r" in CONJ.md sec2)
#   (I2)  D* = #distinct nonzero gamma + [exists gamma=0]
#   (I3)  orbit identity: every nonzero gamma-orbit under x->g*x (g=domain gen^d, d=gcd(e-f,n))
#         has size n/d; O_P = #distinct J=gamma^{n/d}; D* = (n/d)*O_P + [gamma=0].
#   (I4)  O_P <= C(n/2, r-1)  (the single open obligation).
#
# Calibration anchor (CONJ.md, full monomial sweep, faithful BabyBear):
#   n=16 r=3..8 worst #bad = 97,145,89,113,225,104  (maximizers (8,7),(8,5),(9,15),(8,10),(10,15),(9,11))
#   K = 2^r * C(n/2, r) = 448,1120,1792,1792,1024,256

from math import comb, gcd
from itertools import combinations

P1 = 2013265921          # BabyBear, 2^27 | p-1
P2 = 3221225473          # cross prime, 2^30 | p-1

def mu_n(n, p):
    assert (p - 1) % n == 0
    e = (p - 1) // n
    for c in range(2, 600):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return [pow(h, i, p) for i in range(n)], h
    raise RuntimeError("no generator")

def h_series(elts, mmax, p):
    """complete homogeneous h_0..h_mmax of multiset elts via H *= 1/(1-z t)."""
    H = [0] * (mmax + 1); H[0] = 1
    for z in elts:
        # H *= 1/(1-z t):  newH[m] = H[m] + z*newH[m-1]; ASCENDING uses updated H[m-1].
        for m in range(1, mmax + 1):
            H[m] = (H[m] + z * H[m - 1]) % p
    return H

def census_line(dom, n, p, r, e, f):
    """returns (fiber: gamma->count, has_gamma_zero, e1_set) for this monomial line."""
    a = r + 1
    ie, ie1, jf, jf1 = e - r, e - r + 1, f - r, f - r + 1
    if min(ie, ie1, jf, jf1) < 0:
        return None
    mmax = max(ie, ie1, jf, jf1)
    fiber = {}
    has_zero = False
    e1_of_gamma = {}     # gamma -> set of e1(S) values that pin to it (to test gamma=-e1)
    invcache = {}
    for S in combinations(range(n), a):
        elts = [dom[i] for i in S]
        H = h_series(elts, mmax, p)
        he, he1, hf, hf1 = H[ie], H[ie1], H[jf], H[jf1]
        if (he * hf1 - hf * he1) % p != 0:
            continue
        if hf % p == 0:
            continue
        inv = invcache.get(hf)
        if inv is None:
            inv = pow(hf, p - 2, p); invcache[hf] = inv
        g = (-he * inv) % p
        e1 = sum(elts) % p
        if g == 0:
            has_zero = True
        else:
            fiber[g] = fiber.get(g, 0) + 1
            e1_of_gamma.setdefault(g, set()).add(e1)
    return fiber, has_zero, e1_of_gamma

def orbit_count(fiber, n, d, p, gen):
    """O_P = #distinct J = gamma^{n/d}.  also verify orbit sizes = n/d."""
    g_d = pow(gen, d, p)         # generator of the size-(n/d) cyclic dilation group
    period = n // d
    Js = {}
    seen = set()
    orbit_sizes = []
    gammas = set(fiber.keys())
    for gamma in list(gammas):
        if gamma in seen:
            continue
        # build orbit gamma * g_d^j
        orb = set()
        cur = gamma
        for _ in range(period):
            orb.add(cur)
            cur = (cur * g_d) % p
        orbit_sizes.append(len(orb))
        for x in orb:
            seen.add(x)
        J = pow(gamma, period, p)
        Js[J] = Js.get(J, 0) + 1
    return len(Js), orbit_sizes

def worst_over_lines(n, p, r, full=True):
    dom, gen = mu_n(n, p)
    a = r + 1
    best = -1; best_ef = None; best_data = None
    # full monomial sweep: all (e,f) with e>f>=0, e<n, e>=r, f>=r-? ; need indices >=0
    ef_list = []
    for e in range(r, n):
        for f in range(0, e):
            if e - r >= 0 and f - r + 1 >= 0 and f - r >= 0 and e - r + 1 >= 0:
                ef_list.append((e, f))
    if not full:
        # restrict to e=n/2 row + known corners for speed
        ef_list = [(e, f) for (e, f) in ef_list if e == n // 2] + \
                  [(n // 2, n // 2 - 1), (n // 2 + 1, n - 1), (n // 2, n // 2 + 2 if n//2+2<n else n-1)]
    for (e, f) in ef_list:
        res = census_line(dom, n, p, r, e, f)
        if res is None:
            continue
        fiber, has_zero, e1map = res
        nbad = len(fiber) + (1 if has_zero else 0)
        if nbad > best:
            best = nbad; best_ef = (e, f); best_data = (fiber, has_zero, e1map)
    return best, best_ef, best_data, dom, gen

if __name__ == "__main__":
    print("=== D* = worst-over-line #bad-scalar(n,r), full monomial sweep ===")
    print("anchor n=16: r=3..8 -> 97,145,89,113,225,104")
    for n in [16]:
        for r in range(3, 9):
            best, ef, data, dom, gen = worst_over_lines(n, P1, r, full=True)
            fiber, has_zero, e1map = data
            d = gcd(abs(ef[0] - ef[1]), n)
            OP, osizes = orbit_count(fiber, n, d, P1, gen)
            K = (1 << r) * comb(n // 2, r)
            Cbound = comb(n // 2, r - 1)
            # test gamma = -e1 : for every gamma, is the e1-set a singleton equal to -gamma?
            gamma_eq_e1 = all(len(s) == 1 and (list(s)[0] == (-g) % P1) for g, s in e1map.items())
            print(f"  n={n} r={r}: D*={best} at (x^{ef[0]},x^{ef[1]}) d={d} "
                  f"O_P={OP} C(n/2,r-1)={Cbound} K={K} "
                  f"orbsizes={set(osizes)} gamma=-e1:{gamma_eq_e1}")
