#!/usr/bin/env python3
"""
probe_444_max_singleton_allwords.py  (#444 CRACK D)

Sharper question than the worst-LIST word: across ALL structured words and ALL their
list-codewords, what is the MAXIMUM singleton-fiber count s(S) achievable at fixed rho,
and does it GROW with n?  This is the direct test of the task's conjecture #4:

  "the worst window word has at most kappa = O(1) singleton fibers."

We test the contrapositive search: is there ANY word whose list contains a codeword with
many singleton fibers? If max-s stays bounded as n grows -> floor survives; if it grows
-> floor refuted.

Key refinement: we hold k = round(rho*n) small enough that C(n,k) is enumerable, and we
report, per (n, rho):
  - global_max_s : max over all words, all list codewords, of s(S)
  - the agreement budget identity a = 2|B| + |O1|, so s(S)=|O1| <= a = agreement <= n.
  - the THEORETICAL cap: a codeword of degree<k that is z->-z symmetric forces |O1| even
    structure... we just measure.
Words tried: consecutive x^a+x^{a-1} (all a), two-exponent x^a+x^b, and a "singleton-maximal"
adversarial family x^a*(1+x) for all a (= the dossier worst).
"""
import itertools, sys
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta); base = target - (target % n) + 1; p = base
    while True:
        if p > n and isprime(p) and (p-1) % n == 0 and (p-1)//n >= idx_min: return p
        p += n

def subgroup(n, p):
    g = primitive_root(p); zeta = pow(g, (p-1)//n, p); elts, x = [], 1
    for _ in range(n): elts.append(x); x = (x*zeta) % p
    assert len(set(elts)) == n
    return elts

def neg_map(elts, p):
    pos = {v: i for i, v in enumerate(elts)}
    return [pos[(p-v) % p] for v in elts]

def pmul(a, b, p):
    r = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b): r[i+j] = (r[i+j]+ai*bj) % p
    return r

def pcoeffs(xs, ys, p):
    k = len(xs); coeffs = [0]*k
    for i in range(k):
        num, den = [1], 1
        for j in range(k):
            if j == i: continue
            num = pmul(num, [(-xs[j]) % p, 1], p); den = (den*((xs[i]-xs[j]) % p)) % p
        sc = (ys[i]*pow(den, p-2, p)) % p
        for t in range(len(num)): coeffs[t] = (coeffs[t]+sc*num[t]) % p
    return tuple(coeffs)

def evalp(c, x, p):
    v = 0
    for cc in reversed(c): v = (v*x+cc) % p
    return v

def list_codewords(uv, elts, k, s, p):
    n = len(elts); idxs = list(range(n)); seen = {}
    for T in itertools.combinations(idxs, k):
        xs = [elts[i] for i in T]; ys = [uv[i] for i in T]
        c = pcoeffs(xs, ys, p)
        if c in seen: continue
        agree = tuple(i for i in idxs if evalp(c, elts[i], p) == uv[i])
        if len(agree) >= s: seen[c] = agree
    return seen

def fiber_singletons(agree, neg):
    aset = set(agree); seen_f = set(); singles = 0
    for i in agree:
        f = frozenset((i, neg[i]))
        if f in seen_f: continue
        seen_f.add(f)
        if not (i in aset and neg[i] in aset): singles += 1
    return singles

def run(n, beta=4.0, rhos=(0.25, 0.125, 0.0625)):
    p = find_window_prime(n, beta); elts = subgroup(n, p); neg = neg_map(elts, p)
    print(f"n={n} (mu={n.bit_length()-1}) p={p} m={(p-1)//n}", flush=True)
    for rho in rhos:
        k = max(1, round(rho*n))
        if k >= n: continue
        # enumeration budget guard
        from math import comb
        if comb(n, k) > 2_500_000:
            print(f"    rho={rho:.4f} k={k}: SKIP (C(n,k)={comb(n,k)} too big)", flush=True); continue
        eta = rho; s = round((rho+eta)*n)
        if s < k: s = k
        if s > n: continue
        words = {}
        for a in range(2, n): words[f"x^{a}+x^{a-1}"] = [(pow(x,a,p)+pow(x,a-1,p)) % p for x in elts]
        for a in range(1, n):
            for b in range(a+1, n): words[f"x^{a}+x^{b}"] = [(pow(x,a,p)+pow(x,b,p)) % p for x in elts]
        gmax_s = 0; gmax_L = 0; arg = None
        for name, uv in words.items():
            lst = list_codewords(uv, elts, k, s, p)
            if len(lst) > gmax_L: gmax_L = len(lst)
            for ag in lst.values():
                si = fiber_singletons(ag, neg)
                if si > gmax_s: gmax_s = si; arg = (name, len(ag))
        print(f"    rho={rho:.4f} k={k} s={s}: max_L={gmax_L}  GLOBAL_max_s(S)={gmax_s}  "
              f"(at {arg})", flush=True)

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [8, 16, 32]
    for n in ns: run(n)
