#!/usr/bin/env python3
"""
probe_444_consec_singleton_scaling.py  (#444 CRACK D — the decisive scaling test)

Focus ONLY on the dossier worst word family x^a + x^{a-1} (consecutive), and measure how
the singleton-fiber count s(S) of its list-codewords scales with n = 2^mu. This is the
sharp test of the task conjecture: "the worst window word has at most kappa=O(1) singletons."

For each n in {8,16,32,64,128} and each consecutive word x^a+x^{a-1} (all a in 2..n-1),
at rho in {1/4, 1/8} (k = round(rho*n), agreement threshold s = round(2*rho*n)):
  - enumerate the FULL list (deg<k polys agreeing on >= s points), but only over the
    consecutive-word family (n-2 words, polynomial work);
  - report, over the union of all consecutive words' lists at this (n,rho):
      max_s  = max singleton-fiber count s(S),  L_max = max single-word list size.
We skip (n,rho) when C(n,k) > BUDGET to stay feasible. To reach larger n we use the
smallest enumerable rho (k=2,3) so the scaling of s(S) is visible to n=128.
"""
import itertools, sys
from math import comb
from sympy import isprime, primitive_root

BUDGET = 4_000_000

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

def singletons(agree, neg):
    aset = set(agree); seen_f = set(); s = 0
    for i in agree:
        f = frozenset((i, neg[i]))
        if f in seen_f: continue
        seen_f.add(f)
        if not (i in aset and neg[i] in aset): s += 1
    return s

def run(n, beta=4.0, rhos=(0.25, 0.125, 0.0625)):
    p = find_window_prime(n, beta); elts = subgroup(n, p); neg = neg_map(elts, p)
    print(f"n={n:4d} (mu={n.bit_length()-1}) p={p}", flush=True)
    for rho in rhos:
        k = max(1, round(rho*n))
        if k >= n: continue
        if comb(n, k) > BUDGET:
            print(f"    rho={rho:.4f} k={k}: SKIP C(n,k)={comb(n,k)}", flush=True); continue
        s = round(2*rho*n)
        if s < k: s = k
        if s > n: continue
        max_s = 0; L_max = 0; nonsym_words = 0
        for a in range(2, n):
            uv = [(pow(x,a,p)+pow(x,a-1,p)) % p for x in elts]
            lst = list_codewords(uv, elts, k, s, p)
            if not lst: continue
            L_max = max(L_max, len(lst))
            wmax = 0
            for ag in lst.values():
                si = singletons(ag, neg); wmax = max(wmax, si); max_s = max(max_s, si)
            if wmax > 0: nonsym_words += 1
        print(f"    rho={rho:.4f} k={k} s={s}: L_max={L_max}  MAX_s(S)={max_s}  "
              f"#words_with_singletons={nonsym_words}", flush=True)

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [8, 16, 32, 64, 128]
    for n in ns: run(n)
