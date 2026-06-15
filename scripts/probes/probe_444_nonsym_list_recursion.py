#!/usr/bin/env python3
"""
probe_444_nonsym_list_recursion.py  (#444, δ* assault)

GOAL: independently reproduce the load-bearing POSITIVE signal of the campaign --
"on true 2-power (prize) n the worst-case window list is CONSTANT at fixed (rho,eta)"
-- and measure the symmetric (S = -S) vs NON-symmetric agreement-set split, which is
the one open gap in the antipodal-dyadic-tower route (the only off-BGK floor hope).

Method (exact, small parameters, multi-prime):
  * window prize-shaped prime p ~ n^beta, p == 1 (mod n), proper subgroup mu_n (n != p-1).
  * mu_n = order-n multiplicative subgroup of F_p* (n = 2^mu).
  * received word u : mu_n -> F_p, several structured candidates.
  * agreement threshold s = (rho + eta) * n  (window-interior radius delta = 1-rho-eta).
  * FULL list = { deg<k polynomials f : #{x in mu_n : f(x)=u(x)} >= s }.
    Enumerated EXACTLY by interpolating every k-subset and testing agreement (feasible
    for small k = rho*n).
  * For the worst word, classify each list codeword's MAXIMAL agreement set S by whether
    S = -S (antipodal-symmetric, captured by the squaring tower) or not.

No fabrication: exact arithmetic mod p, multiple primes, proper subgroups, never n=p-1,
correlated directions x^{n/2}=+-1 flagged.
"""
import itertools, sys
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    """smallest prime p == 1 mod n with p >= n^beta (proper subgroup, m=(p-1)/n>1)."""
    target = int(n ** beta)
    # start at a multiple of n above target
    base = target - (target % n) + 1
    p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min:
            return p
        p += n

def subgroup(n, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // n, p)            # primitive n-th root of unity
    elts = []
    x = 1
    for _ in range(n):
        elts.append(x)
        x = (x * zeta) % p
    assert len(set(elts)) == n, "subgroup degenerate"
    return elts, zeta

def neg_index_map(elts, p):
    """for x = elts[i], index of -x in elts (antipode)."""
    pos = {v: i for i, v in enumerate(elts)}
    return [pos[(p - v) % p] for v in elts]

def lagrange_interp_value(xs, ys, p, xq):
    """value at xq of the deg<len(xs) interpolant through (xs,ys), mod p."""
    total = 0
    k = len(xs)
    for i in range(k):
        num = ys[i] % p
        den = 1
        for j in range(k):
            if j == i:
                continue
            num = (num * ((xq - xs[j]) % p)) % p
            den = (den * ((xs[i] - xs[j]) % p)) % p
        total = (total + num * pow(den, p - 2, p)) % p
    return total

def poly_coeffs(xs, ys, p):
    """deg<k interpolant coefficients (low->high) for hashing identity of codewords."""
    k = len(xs)
    # Newton / Lagrange to coeffs via simple O(k^2) build
    coeffs = [0] * k
    for i in range(k):
        # basis poly L_i(x) = prod_{j!=i} (x - xs[j])/(xs[i]-xs[j])
        num = [1]
        den = 1
        for j in range(k):
            if j == i:
                continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = (den * ((xs[i] - xs[j]) % p)) % p
        inv = pow(den, p - 2, p)
        scale = (ys[i] * inv) % p
        for t in range(len(num)):
            coeffs[t] = (coeffs[t] + scale * num[t]) % p
    return tuple(coeffs)

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r

def full_list(uvals, elts, k, s, p):
    """all deg<k polys agreeing with u on >= s points of mu_n. returns {coeffs: agree_set}."""
    n = len(elts)
    idxs = list(range(n))
    seen = {}
    for T in itertools.combinations(idxs, k):
        xs = [elts[i] for i in T]
        ys = [uvals[i] for i in T]
        c = poly_coeffs(xs, ys, p)
        if c in seen:
            continue
        # agreement set
        agree = tuple(i for i in idxs if lagrange_interp_value(xs, ys, p, elts[i]) == uvals[i])
        if len(agree) >= s:
            seen[c] = agree
    return seen

def word_consecutive(elts, a, p):
    return [(pow(x, a, p) + pow(x, a - 1, p)) % p for x in elts]

def word_two_exp(elts, a, b, p):
    return [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]

def classify_symmetry(agree, neg):
    aset = set(agree)
    return all(neg[i] in aset for i in agree)

def run(n, beta=4.0, eta_frac=None, rhos=(0.25, 0.125, 0.0625)):
    print(f"\n========== n={n} (mu={n.bit_length()-1}) ==========")
    primes = []
    p1 = find_window_prime(n, beta)
    primes.append(p1)
    # a second, structurally different prime (slightly higher beta) for p-independence check
    p2 = find_window_prime(n, beta + 0.4)
    if p2 != p1:
        primes.append(p2)
    for p in primes:
        elts, zeta = subgroup(n, p)
        neg = neg_index_map(elts, p)
        m = (p - 1) // n
        print(f"  p={p}  beta~={(p.bit_length()/ (n.bit_length()-1)) if n>1 else 0:.2f}  "
              f"m=(p-1)/n={m}  v2(p-1)={bin((p-1)).count('0' )}")
        for rho in rhos:
            k = max(1, round(rho * n))
            if k >= n:
                continue
            # window interior eta: use eta = rho (dossier midpoint) unless overridden
            eta = eta_frac if eta_frac is not None else rho
            s = round((rho + eta) * n)
            if s < k:
                s = k
            if s > n:
                continue
            # guard: skip if the k-subset enumeration is too large
            from math import comb
            if comb(n, k) > 2_000_000:
                print(f"    rho={rho:.4f} k={k} s={s}: SKIP (C(n,k)={comb(n,k)} too large)")
                continue
            # candidate worst words (trimmed for speed at large n)
            cands = {}
            # consecutive-exponent family (dossier worst at rho<1/4)
            for a in range(2, n):
                cands[f"x^{a}+x^{a-1}"] = word_consecutive(elts, a, p)
            # both-odd family with small leading exponent (dossier worst at rho=1/4)
            for a in range(1, min(n, 6), 2):
                for b in range(a + 2, n, 2):
                    cands[f"x^{a}+x^{b}(odd)"] = word_two_exp(elts, a, b, p)
            worst = (-1, None, None)
            for name, uv in cands.items():
                # skip correlated directions: words that are pure x^{n/2} multiples -> exclude exps == n/2
                lst = full_list(uv, elts, k, s, p)
                if len(lst) > worst[0]:
                    worst = (len(lst), name, lst)
            L, wname, wlist = worst
            # symmetry split of the worst word's list
            nsym = sum(1 for ag in wlist.values() if classify_symmetry(ag, neg))
            print(f"    rho={rho:.4f} k={k} s={s} (eta={eta:.3f}) -> "
                  f"WORST list L={L}  word={wname}  sym/total={nsym}/{L}")

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [16, 32]
    for n in ns:
        run(n)
