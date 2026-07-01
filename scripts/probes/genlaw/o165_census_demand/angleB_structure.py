# Angle B structure probe: understand gamma as a function on the half, and the descent.
#
# Squaring map sq: mu_n -> mu_{n/2}, z->z^2, fiber {w,-w}.  -1 = w0^{n/2} (the order-2 elt).
# A pair-class is {w,-w}; sq sends it to w^2 in mu_{n/2}.
#
# Descent generating function. For S subset mu_n, split:
#   - PAIRS: indices i where BOTH z_i and -z_i are in S (a full antipodal pair {w,-w}).
#   - SINGLETONS: z in S with -z NOT in S.
# prod_{z in S} 1/(1-z t) = prod_{pairs} 1/(1-w^2 t^2) * prod_{singletons} 1/(1-z t).
# => generating function in t factors. h_m(S) = sum over how degree m splits between
#    the EVEN part (from pairs, only even powers of t) and the singleton part.
#
# Let SQ = multiset of w^2 for pairs (in mu_{n/2}), T = multiset of singletons (in mu_n).
#   Heven(t^2) = prod_{pairs} 1/(1-w^2 t^2) = sum_s h_s(SQ) t^{2s}
#   Hsing(t)   = prod_{singletons} 1/(1-z t) = sum_j h_j(T) t^j
#   h_m(S) = sum_{2s + j = m} h_s(SQ) * h_j(T)   = sum_s h_s(SQ) h_{m-2s}(T).   [the hint]
#
# We want to express gamma = -h_{e-r}(S)/h_{f-r}(S) and find a canonical signed r-subset.

from math import comb, gcd
from itertools import combinations
import sys

p = 2013265921

def mu_n(n, pp):
    e = (pp - 1) // n
    for c in range(2, 400):
        h = pow(c, e, pp)
        if pow(h, n, pp) == 1 and pow(h, n // 2, pp) != 1:
            return [pow(h, i, pp) for i in range(n)]
    raise RuntimeError

def h_powersums(elts, mmax, pp):
    L = len(elts)
    P = [L % pp] + [0]*(mmax)
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

def analyze_structure(n, r, e, f, pp):
    dom = mu_n(n, pp)
    idx = {dom[i]: i for i in range(n)}
    neg1 = dom[n//2]  # the order-2 element = -1
    a = r + 1
    me, mf, me1, mf1 = e-r, f-r, e-r+1, f-r+1
    mmax = max(me, mf, me1, mf1)
    # for each bad S with nonzero finite gamma, record: gamma, #pairs, #singletons, sorted gamma
    by_gamma = {}
    for S in combinations(range(n), a):
        elts = [dom[i] for i in S]
        H = h_powersums(elts, mmax, pp)
        he, hf, he1, hf1 = H[me], H[mf], H[me1], H[mf1]
        if (he*hf1 - hf*he1) % pp != 0:
            continue
        if hf % pp == 0:
            continue
        g = (-he * pow(hf, pp-2, pp)) % pp
        if g == 0:
            continue
        # antipodal structure of S
        Sset = set(S)
        npairs = 0
        singles = []
        seen = set()
        for i in S:
            if i in seen: continue
            j = idx[(dom[i]*neg1) % pp]  # index of -z
            if j in Sset:
                npairs += 1
                seen.add(i); seen.add(j)
            else:
                singles.append(i); seen.add(i)
        by_gamma.setdefault(g, []).append((npairs, len(singles), tuple(sorted(S))))
    return by_gamma, dom, neg1, idx

if __name__ == "__main__":
    n = 16; r = 3; e, f = n//2, n//2-1
    by_gamma, dom, neg1, idx = analyze_structure(n, r, e, f, p)
    print(f"n={n} r={r} line(x^{e},x^{f}): #distinct nonzero gamma = {len(by_gamma)}")
    # fiber-size distribution
    from collections import Counter
    fs = Counter(len(v) for v in by_gamma.values())
    print("fiber-size dist {size:#gammas}:", dict(sorted(fs.items())))
    # For a few gammas, show antipodal composition of their fibers
    print("\nSample gamma fibers (npairs, nsingles per subset):")
    for gi, (g, lst) in enumerate(sorted(by_gamma.items())):
        if gi >= 6: break
        comp = Counter((np_, ns) for (np_, ns, _) in lst)
        print(f"  gamma={g}: fiber={len(lst)}  (npairs,nsing)->count: {dict(comp)}")
    # Is gamma always an n/2-th power / in mu_{n/2}? Check gamma^{n/2}, gamma^n
    print("\ngamma in which subgroup?")
    for gi, g in enumerate(sorted(by_gamma)):
        if gi >= 8: break
        ords = []
        gg = g
        # find multiplicative order dividing? check g^n, g^{n/2}
        print(f"  g={g}: g^{n}={pow(g,n,p)} g^{n//2}={pow(g,n//2,p)} g^{n*2}={pow(g,2*n,p)}")
