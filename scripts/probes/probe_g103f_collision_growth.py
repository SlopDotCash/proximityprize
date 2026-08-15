#!/usr/bin/env python3
"""G103F probe: exact max_c #(H ∩ (H+c)) for multiplicative subgroups H = mu_n of F_p,
n = 16..1024, across beta = log_n p in {2,3,4}. Extends G102F's rho<=6 data; measures the
truth-vs-classical gap (classical Stepanov/HBK bound ~ 4(2n)^{2/3}; formalized parametric
bound 4B^2 for any B with 2B <= n <= B^3/2, nB <= p)."""
import sys
from collections import Counter

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def factor(n):
    fs = {}
    d = 2
    while d*d <= n:
        while n % d == 0: fs[d] = fs.get(d,0)+1; n //= d
        d += 1
    if n > 1: fs[n] = fs.get(n,0)+1
    return fs

def primitive_root(p):
    fs = factor(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs):
            return g
    raise RuntimeError

def first_prime(n, lo):
    # smallest prime p >= lo with p = 1 mod n
    p = lo + ((1 - lo) % n)
    if p < lo: p += n
    while not is_prime(p): p += n
    return p

def best_formal_bound(n, p):
    best = None
    B = 2
    while B*B*B <= 10**18 and 2*B <= n:
        if 2*n <= B*B*B and n*B <= p:
            best = 4*B*B
            break  # smallest valid B gives smallest 4B^2
        B += 1
    return best

print(f"{'n':>5} {'beta':>4} {'p':>14} {'rho=max_c':>9} {'mean_r':>7} "
      f"{'n^(2/3)':>8} {'rho/n^2/3':>9} {'4B^2':>7} {'trivial n':>9}")
for n in [16, 32, 64, 128, 256, 512, 1024]:
    for beta in [2, 3, 4]:
        lo = n**beta
        p = first_prime(n, max(lo, 2*n+1))
        g = primitive_root(p)
        h = pow(g, (p-1)//n, p)
        H, x = [], 1
        for _ in range(n):
            H.append(x); x = x*h % p
        assert len(set(H)) == n
        Hs = set(H)
        diffs = Counter()
        for a in H:
            for b in H:
                if a != b:
                    diffs[(a-b) % p] += 1
        rho = max(diffs.values())
        mean = sum(diffs.values())/len(diffs)
        fb = best_formal_bound(n, p)
        print(f"{n:>5} {beta:>4} {p:>14} {rho:>9} {mean:>7.2f} "
              f"{n**(2/3):>8.1f} {rho/n**(2/3):>9.3f} {str(fb):>7} {n:>9}", flush=True)
print("done")
