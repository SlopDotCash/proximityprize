"""
probe_444_r6_measure.py  (#444 -- MEASURE task, r=6: #{S on V}, #bad, K, gamma-fibers, V structure)

DEEP BAND depth r: agreement a0=r+1, codeword deg k=r-1, deficit 2. Witness LINE (x^e,x^f).
CLEAN REDUCTION (proven): (r+1)-subset S of mu_n is BAD for line (x^e,x^f) <=>
    h_{e-r}(S) * h_{f-r+1}(S) = h_{f-r}(S) * h_{e-r+1}(S)    (variety V)
and gamma = - h_{e-r}(S) / h_{f-r}(S)  (pinned bad scalar).

We compute the h_m via Newton's identity from power sums of S (h_m = complete homogeneous).
This MUST reproduce the r=3 calibration (#bad = n*C(n/4,2)+1, O_P = C(n/4,2) = 6,28 @ n=16,32)
and match the interpolation-based bad-set count of probe_444_antipodal_law.py before trusting.

Then: find the TRUE r=6 maximizer line (target O_P=14 @ n=16, 185 @ n=32), and report:
  (1) #{S on V} = number of bad (r+1)-subsets
  (2) #bad = #distinct nonzero gamma ; K = 2^r C(n/2,r) ; checks
  (3) gamma-fiber size distribution
  (4) structure of V.
"""
import itertools
from math import comb, gcd
from collections import Counter, defaultdict

p = 2013265921          # BabyBear, 2^27 | p-1
p2 = 3221225473         # cross-check prime, 2^30 | p-1

def w_of_order(n, pr):
    e = (pr - 1) // n
    for c in range(2, 2000):
        h = pow(c, e, pr)
        if pow(h, n, pr) == 1 and pow(h, n // 2, pr) != 1:
            return h
    raise RuntimeError("no w")

def complete_homog(S, mmax, pr):
    """h_0..h_mmax for the multiset S (here a set of distinct roots), via Newton-like recursion.
    Generating function prod 1/(1-z t) = sum h_m t^m. Power sums P_j = sum z^j.
    h_m = (1/m) sum_{i=1}^m P_i h_{m-i}, h_0 = 1."""
    # power sums P_1..P_mmax
    P = [0] * (mmax + 1)
    for z in S:
        zi = 1
        for j in range(1, mmax + 1):
            zi = (zi * z) % pr
            P[j] = (P[j] + zi) % pr
    h = [0] * (mmax + 1)
    h[0] = 1
    for m in range(1, mmax + 1):
        s = 0
        for i in range(1, m + 1):
            s = (s + P[i] * h[m - i]) % pr
        h[m] = (s * pow(m, pr - 2, pr)) % pr
    return h

def measure(n, r, e, f, pr=p, want_fibers=True):
    w = w_of_order(n, pr); mu = [pow(w, i, pr) for i in range(n)]
    a0 = r + 1
    # h-indices needed: e-r, e-r+1, f-r, f-r+1  (must be >=0 for the identity to be valid)
    idxs = [e - r, e - r + 1, f - r, f - r + 1]
    mmax = max(idxs)
    if min(idxs) < 0:
        return None  # line not admissible for this reduction form
    K = (1 << r) * comb(n // 2, r)
    d = gcd((e - f) % n, n); mult = pow(w, (e - f) % n, pr)
    inv = lambda x: pow(x, pr - 2, pr)

    S_on_V = 0
    zero_bad = 0
    fiber = defaultdict(list)   # gamma -> list of S (indices) ; only nonzero gamma
    for Sidx in itertools.combinations(range(n), a0):
        S = [mu[i] for i in Sidx]
        h = complete_homog(S, mmax, pr)
        he_r   = h[e - r];   he_r1 = h[e - r + 1]
        hf_r   = h[f - r];   hf_r1 = h[f - r + 1]
        # variety V: h_{e-r} h_{f-r+1} == h_{f-r} h_{e-r+1}
        if (he_r * hf_r1 - hf_r * he_r1) % pr != 0:
            continue
        S_on_V += 1
        # pinned gamma = - h_{e-r}/h_{f-r}  (if h_{f-r} != 0); else degenerate handling
        if hf_r % pr != 0:
            gam = (-he_r * inv(hf_r)) % pr
        else:
            # h_{f-r}=0; on V this forces h_{e-r} h_{f-r+1}=0. gamma via the other ratio:
            # gamma = -h_{e-r+1}/h_{f-r+1} when h_{f-r+1}!=0
            if hf_r1 % pr != 0:
                gam = (-he_r1 * inv(hf_r1)) % pr
            else:
                gam = None  # fully degenerate; count separately
        if gam is None:
            continue
        if gam == 0:
            zero_bad += 1
            continue
        if want_fibers:
            fiber[gam].append(Sidx)
        else:
            fiber[gam] = fiber.get(gam, 0) + 1

    if want_fibers:
        nbad = len(fiber)
        fibsizes = Counter(len(v) for v in fiber.values())
    else:
        nbad = len(fiber)
        fibsizes = Counter(fiber.values())
    return dict(n=n, r=r, e=e, f=f, a0=a0, K=K, d=d, mult=mult,
                S_on_V=S_on_V, zero_bad=zero_bad, nbad=nbad,
                fibsizes=fibsizes, fiber=fiber if want_fibers else None,
                orbit_size=n // d)

if __name__ == "__main__":
    print("=== CALIBRATION r=3 (must match #bad=n*C(n/4,2), O_P=6,28) ===")
    for n in [16, 32]:
        e, f = n // 2, n // 2 - 1   # (x^{n/2}, x^{n/2-1}) the r=3 resonant line
        res = measure(n, 3, e, f, want_fibers=False)
        print(f"n={n} r=3 line(x^{e},x^{f}): S_on_V={res['S_on_V']} #bad={res['nbad']} "
              f"zero={res['zero_bad']} K={res['K']} expect #bad={n*comb(n//4,2)}")
