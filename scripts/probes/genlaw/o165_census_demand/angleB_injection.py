# Angle B: INJECTION of distinct nonzero bad-gamma into signed r-subsets of mu_{n/2}.
# K = 2^r * C(n/2, r) = #{signed r-subsets of the half mu_{n/2}}.
#
# Model (THIS task = bilinear Schur-ratio line model):
#   mu_n = order-n subgroup of F_p*, n = 2^mu, p == 1 mod n, large prime (char-0 worst case).
#   Witness line (x^e, x^f). An (r+1)-subset S of mu_n is BAD <=>
#       h_{e-r}(S) * h_{f-r+1}(S) = h_{f-r}(S) * h_{e-r+1}(S)   (variety V)
#   and then gamma = - h_{e-r}(S) / h_{f-r}(S)  (the det-kernel direction).
#   h_m = complete-homogeneous symmetric poly = [t^m] prod_{z in S} 1/(1-z t).
#
# DESCENT CONVOLUTION: write S as antipodal structure. mu_n has the squaring map
# sq: z -> z^2 sending mu_n onto mu_{n/2} (2-to-1, fibers {w, -w}).
#   h_m(S) = sum_s h_s(SQ) * h_{m-2s}(T)?   <- the prompt's hint; VERIFY exact form.
# Actually the clean descent is over generating functions:
#   prod_{z in S} 1/(1-z t).  If S is a union of antipodal PAIRS {w,-w}: each pair
#   contributes 1/((1-wt)(1+wt)) = 1/(1 - w^2 t^2).  A singleton z contributes 1/(1-zt).
#
# Here we just MEASURE and try to build the injection. First: reproduce r=3 calibration.

from math import comb
from itertools import combinations
import sys

p = 2013265921  # BabyBear, 2^27 | p-1
p2 = 3221225473 # cross-check prime

def mu_n(n, pp):
    e = (pp - 1) // n
    for c in range(2, 400):
        h = pow(c, e, pp)
        if pow(h, n, pp) == 1 and pow(h, n // 2, pp) != 1:
            return [pow(h, i, pp) for i in range(n)]
    raise RuntimeError("no generator")

def h_powersums(elts, mmax, pp):
    # power sums P_i = sum z^i, i=1..mmax  (P_0 = len)
    # h_m = (1/m) sum_{i=1}^m P_i h_{m-i},  h_0 = 1   (Newton)
    L = len(elts)
    P = [L % pp] + [0]*(mmax)
    # precompute powers
    cur = [1]*L
    for i in range(1, mmax+1):
        s = 0
        for j in range(L):
            cur[j] = (cur[j]*elts[j]) % pp
            s += cur[j]
        P[i] = s % pp
    H = [1] + [0]*mmax
    for m in range(1, mmax+1):
        acc = 0
        for i in range(1, m+1):
            acc = (acc + P[i]*H[m-i]) % pp
        H[m] = (acc * pow(m, pp-2, pp)) % pp
    return H

def h_via_genfunc(elts, mmax, pp):
    # direct: prod 1/(1-z t) mod t^{mmax+1}, coefficients = h_m. Cross-check.
    H = [1] + [0]*mmax
    for z in elts:
        # multiply by 1/(1-z t) = sum z^k t^k  -> H_new[m] = sum_{k<=m} z^k H[m-k]
        newH = [0]*(mmax+1)
        zk = 1
        # convolution with geometric series: newH[m] = H[m] + z*newH[m-1]
        newH[0] = H[0]
        for m in range(1, mmax+1):
            newH[m] = (H[m] + z*newH[m-1]) % pp
        H = newH
    return H

def bad_gammas(n, r, e, f, pp, verbose=False):
    """Return (set of distinct nonzero gamma, count gamma=0 subsets, count hf=0(inf) subsets,
              dict gamma->list of subsets for fiber analysis)."""
    dom = mu_n(n, pp)
    a = r + 1
    me = e - r        # h_{e-r}
    mf = f - r        # h_{f-r}
    me1 = e - r + 1
    mf1 = f - r + 1
    mmax = max(me, mf, me1, mf1)
    if min(me, mf, me1, mf1) < 0:
        raise ValueError(f"negative h index: me={me},mf={mf}")
    gammas = set()
    gzero = 0
    ginf = 0
    fibers = {}
    for S in combinations(range(n), a):
        elts = [dom[i] for i in S]
        H = h_powersums(elts, mmax, pp)
        he, hf, he1, hf1 = H[me], H[mf], H[me1], H[mf1]
        # V: he*hf1 == hf*he1
        if (he*hf1 - hf*he1) % pp != 0:
            continue
        # gamma = -he/hf
        if hf % pp == 0:
            if he % pp == 0:
                ginf += 1   # both zero: fully degenerate-ish (both h_{f-r} and h_{e-r}=0)
            else:
                ginf += 1
            continue
        g = (-he * pow(hf, pp-2, pp)) % pp
        if g == 0:
            gzero += 1
            continue
        gammas.add(g)
        fibers.setdefault(g, []).append(S)
    return gammas, gzero, ginf, fibers

if __name__ == "__main__":
    # r=3 calibration. The TRUE r=3 maximizer line for THIS bilinear model.
    # Per detail: r=3 Schur-ratio maximizer line (x^{n/2}, x^{n/2-1}) gives #bad = O_P with O_P=6,28.
    print("=== r=3 CALIBRATION (bilinear Schur-ratio model) ===")
    for n in [16, 32]:
        r = 3
        e, f = n//2, n//2 - 1
        gammas, gz, gi, fib = bad_gammas(n, r, e, f, p)
        K = (1 << r) * comb(n//2, r)
        # O_P = #distinct nonzero gamma / (n/d), d = gcd(e-f,n)
        from math import gcd
        d = gcd(e - f, n)
        nd = n // d
        OP = len(gammas) // nd if nd else 0
        print(f"n={n} line(x^{e},x^{f}) d={d} n/d={nd}: #bad(nz)={len(gammas)} gamma0={gz} inf={gi} "
              f"O_P={len(gammas)/nd:.3f} K={K} C(n/4,2)={comb(n//4,2)}")
