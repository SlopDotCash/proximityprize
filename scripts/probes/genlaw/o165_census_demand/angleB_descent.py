# Angle B descent: express h_m(S) via the squaring descent and try to canonically
# extract a SIGNED r-subset of mu_{n/2} from a bad gamma (or from a bad subset S).
#
# Key counting identity to exploit:
#   K = 2^r * C(n/2, r)  = #{ choose r pair-classes of mu_{n/2}, sign each }.
# Source has r+1 elements but K counts r objects.  The descent must collapse r+1 -> r.
#
# THE PLAN we test:
#   For a bad S, the pinned codeword has degree k=r-1 and agreement a0=r+1, deficit 2.
#   gamma is a single scalar.  We try the map
#       Phi: S |-> (sq(S) as a multiset in mu_{n/2}) together with a sign vector.
#   But |sq(S)| could collapse if S contains antipodal pairs (w,-w -> same square w^2).
#   When S has c pairs and (r+1-2c) singletons, sq(S) has c (doubled) squares + (r+1-2c) squares.
#
# Instead, test the MORE LIKELY injection used in such bounds:
#   distinct nonzero gamma  <->  monic poly of degree <= something / a signed r-subset.
# We just EMPIRICALLY check, at r=3,4,5 and several lines, whether the map
#       gamma |-> (canonical data)  is injective, and count the IMAGE.

from math import comb, gcd
from itertools import combinations
from collections import Counter

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

def collect(n, r, e, f, pp):
    dom = mu_n(n, pp)
    a = r + 1
    me, mf, me1, mf1 = e-r, f-r, e-r+1, f-r+1
    mmax = max(me, mf, me1, mf1)
    # gamma -> list of subsets
    fib = {}
    gzero = 0; ginf = 0
    for S in combinations(range(n), a):
        elts = [dom[i] for i in S]
        H = h_powersums(elts, mmax, pp)
        he, hf, he1, hf1 = H[me], H[mf], H[me1], H[mf1]
        if (he*hf1 - hf*he1) % pp != 0:
            continue
        if hf % pp == 0:
            ginf += 1; continue
        g = (-he*pow(hf,pp-2,pp)) % pp
        if g == 0:
            gzero += 1; continue
        fib.setdefault(g, []).append(S)
    return fib, gzero, ginf, dom

def report(n, r, e, f, pp=p):
    fib, gz, gi, dom = collect(n, r, e, f, pp)
    d = gcd(e-f, n); nd = n//d
    K = (1<<r)*comb(n//2, r)
    nbad = len(fib)
    fs = Counter(len(v) for v in fib.values())
    OP = nbad/nd
    print(f"  n={n} line(x^{e},x^{f}) d={d}: #bad(nz)={nbad} gamma0={gz} inf={gi} "
          f"O_P={OP:.2f} K={K} bad/K={nbad/K:.3f} fiberdist={dict(sorted(fs.items()))}")
    return fib, K

if __name__ == "__main__":
    print("=== gamma-map fiber structure across r, lines ===")
    print("r=3:")
    for n in [16, 32]:
        report(n, 3, n//2, n//2-1)
    print("r=4 (true maximizer line x^{n/2+2}, x^{n/4+1}):")
    for n in [16, 32]:
        report(n, 4, n//2+2, n//4+1)
    print("r=5 (true maximizer x^{n/2+1}, x^{n-1}):")
    for n in [16]:
        report(n, 5, n//2+1, n-1)
    # also r=4 KKH26-style and a couple of generic lines to see when fiber>1
    print("r=4 line x^4,x^3 (small):")
    for n in [16, 32]:
        report(n, 4, 4, 3)
