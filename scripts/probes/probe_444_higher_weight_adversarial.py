#!/usr/bin/env python3
"""
probe_444_higher_weight_adversarial.py  (#444 SEAM A -- Refuter A, deep coefficient search)

Refines probe_444_higher_weight_refuter: for the small enumerable configs, do a MUCH more
thorough search for the worst-case window list among weight-3 and weight-4 words, including:
  * full exponent scan (ones) for weight 3 and (where feasible) weight 4,
  * many random coeff vectors per exponent tuple,
  * a structured "two/three monomial + interference" family designed to MAXIMIZE
    accidental low-degree agreement (the mechanism by which a word's window list grows).

Also reconciles the L=7 vs L=8 baseline by reporting the worst weight-2 list with b ranging
over [0,n) (constant term allowed) vs [1,n).

Exact arithmetic, multiple prize-shaped primes, proper subgroup mu_n (never n=p-1),
window-interior radius. A higher-weight word beating the weight-2 worst (strictly larger or
n-growing faster) REFUTES the low-weight assumption.
"""
import itertools, sys, random
from math import comb
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta); base = target - (target % n) + 1; p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min:
            return p
        p += n

def subgroup(n, p):
    g = primitive_root(p); zeta = pow(g, (p - 1) // n, p)
    elts, x = [], 1
    for _ in range(n):
        elts.append(x); x = (x * zeta) % p
    return elts

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r

def interp_coeffs(xs, ys, p):
    k = len(xs); c = [0] * k
    for i in range(k):
        num = [1]; den = 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p); den = (den * ((xs[i] - xs[j]) % p)) % p
        inv = pow(den, p - 2, p); sc = (ys[i] * inv) % p
        for t in range(len(num)): c[t] = (c[t] + sc * num[t]) % p
    return tuple(c)

def peval(c, x, p):
    r = 0
    for a in reversed(c): r = (r * x + a) % p
    return r

def list_RS(uvals, elts, k, s, p):
    n = len(elts); seen = set()
    for T in itertools.combinations(range(n), k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = interp_coeffs(xs, ys, p)
        if c in seen: continue
        ag = sum(1 for i in range(n) if peval(c, elts[i], p) == uvals[i])
        if ag >= s: seen.add(c)
    return len(seen)

def word_vals(elts, exps, coeffs, p):
    return [sum(coeffs[t] * pow(x, exps[t], p) for t in range(len(exps))) % p for x in elts]

def reconcile_weight2(n, k, eta, beta=4.0):
    """worst weight-2 list with b in [0,n) (constant allowed) -- to pin the L=7/L=8 baseline."""
    p = find_window_prime(n, beta); elts = subgroup(n, p)
    rho = k / n; s = round((rho + eta) * n); s = max(s, k); s = min(s, n)
    h = n // 2
    best_incl0 = (-1, None); best_excl0 = (-1, None)
    for a in range(1, n):
        if a == h: continue
        for b in range(0, a):
            if b == h: continue
            uv = [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]
            L = list_RS(uv, elts, k, s, p)
            if L > best_incl0[0]: best_incl0 = (L, (a, b))
            if b >= 1 and L > best_excl0[0]: best_excl0 = (L, (a, b))
    print(f"  reconcile n={n} k={k} s={s} p={p}: "
          f"worst weight-2 (b>=0)={best_incl0[0]} at {best_incl0[1]} ; "
          f"(b>=1)={best_excl0[0]} at {best_excl0[1]}")
    return s

def worst_over_weight(n, k, eta, weight, beta, exp_iter, n_rand, seed, allow_const=False):
    p = find_window_prime(n, beta); elts = subgroup(n, p)
    rho = k / n; s = round((rho + eta) * n); s = max(s, k); s = min(s, n)
    rng = random.Random(seed)
    h = n // 2
    best = (-1, None, None)
    for exps in exp_iter:
        exps = tuple(exps)
        # exclude pure correlated-direction words (all exps in {0, n/2})
        if all((e % n) in (0, h) for e in exps):
            continue
        # ones
        uv = word_vals(elts, exps, (1,) * weight, p)
        L = list_RS(uv, elts, k, s, p)
        if L > best[0]: best = (L, exps, "ones")
        # random coeffs
        for _ in range(n_rand):
            coeffs = tuple(rng.randrange(1, p) for _ in range(weight))
            uv = word_vals(elts, exps, coeffs, p)
            L = list_RS(uv, elts, k, s, p)
            if L > best[0]: best = (L, exps, coeffs)
    return p, s, best

def run():
    primes = [4.0, 4.4]
    # focus configs (small enough for deep search):
    #  n=16 k=1 (s=2), n=16 k=2 (s=4), n=32 k=1 (s=2)
    configs = [(16, 1, 0.0625), (16, 2, 0.125), (32, 1, 0.03125)]
    for (n, k, eta) in configs:
        print(f"\n########## n={n} k={k} rho={k/n:.4f} eta={eta} ##########")
        s = reconcile_weight2(n, k, eta)
        for beta in primes:
            # weight 3: FULL exponent scan + 6 random coeffs each
            all3 = list(itertools.combinations(range(0 if k>=2 else 1, n), 3))
            p, s, b3 = worst_over_weight(n, k, eta, 3, beta, all3, n_rand=6, seed=101)
            # weight 4: full exp scan if small else 200 sampled, + 6 random coeffs each
            all4 = list(itertools.combinations(range(0 if k>=2 else 1, n), 4))
            rng = random.Random(5)
            samp4 = all4 if len(all4) <= 300 else rng.sample(all4, 300)
            _, _, b4 = worst_over_weight(n, k, eta, 4, beta, samp4, n_rand=6, seed=202)
            print(f"  p={p} s={s}:")
            print(f"    WEIGHT-3 full-exp+rand: worst L={b3[0]} exps={b3[1]} ({'ones' if b3[2]=='ones' else 'rand-coeffs'})")
            print(f"    WEIGHT-4 ({len(samp4)}/{len(all4)} exps)+rand: worst L={b4[0]} exps={b4[1]} ({'ones' if b4[2]=='ones' else 'rand-coeffs'})")

if __name__ == "__main__":
    run()
