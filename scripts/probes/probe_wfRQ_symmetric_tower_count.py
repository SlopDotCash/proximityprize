#!/usr/bin/env python3
"""
probe_wfRQ_symmetric_tower_count.py  (#444 RELATED-QUANTITY: the symmetric-tower bracket)

GOAL. Bank the EXACT symmetric (S = -S) agreement-pattern count L_sym(n,k,s) as a PROVEN
lower bracket on the worst-case MCA list (hence an upper bracket on delta* via
mcaDeltaStar_le_of_bad). The symmetric sub-family is the O1 = empty stratum of the descent
recursion (DescentKernelLemma): agreement a = 2|B| + s(S), with s(S) = 0 exactly when S = -S.

We measure two things and check they AGREE (the self-similarity claim):

 (A)  BRUTE symmetric count.  For a fixed EVEN received word w (w(-x) = w(x)), count the
      distinct degree-<k codewords g whose agreement set S = {x : g(x) = w(x)} is symmetric
      (S = -S) AND has |S| >= s.  These are the words the squaring tower captures exactly.

 (B)  TOWER prediction via descent.  An even word w(x) = w_e(x^2) lifts to a level-1 word
      W := w_e on D1 = mu_{n/2}.  The symmetric-agreement codewords g = glue(e,f) with S=-S
      split per fiber: z in B (g agrees on BOTH +-y), and the agreement budget is 2|B|.
      For an EVEN word, the odd-part constraint on a double fiber is  e(z)=W(z) AND f(z)=0
      ... we test the cleaner EVEN-CODEWORD slice:  restrict to g even (f = 0), g(x)=e(x^2);
      then g symmetric automatically, S=-S, and the agreement set IS the fiber-doubling of
      the level-1 agreement of e with W on D1.  => L_sym(n,k,s) restricted to even codewords
      = L(D1 = mu_{n/2}, ceil(k/2), ceil(s/2))  EXACTLY  (the dyadic self-similar recursion).

We tabulate L_even(n,k,s) and verify  L_even(n,k,s) = L_brute_level1(n/2, ceil(k/2), ceil(s/2)).

Exact arithmetic mod p, prize-shaped primes, proper subgroups (never n = p-1).
"""
import itertools, sys
from sympy import isprime, primitive_root
from math import comb

def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta)
    base = target - (target % n) + 1
    p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min:
            return p
        p += n

def subgroup(n, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // n, p)
    elts, x = [], 1
    for _ in range(n):
        elts.append(x); x = (x * zeta) % p
    assert len(set(elts)) == n
    return elts

def neg_index_map(elts, p):
    pos = {v: i for i, v in enumerate(elts)}
    return [pos[(p - v) % p] for v in elts]

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r

def poly_coeffs(xs, ys, p):
    k = len(xs)
    coeffs = [0] * k
    for i in range(k):
        num, den = [1], 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = (den * ((xs[i] - xs[j]) % p)) % p
        scale = (ys[i] * pow(den, p - 2, p)) % p
        for t in range(len(num)):
            coeffs[t] = (coeffs[t] + scale * num[t]) % p
    return tuple(coeffs)

def eval_poly(coeffs, x, p):
    v = 0
    for c in reversed(coeffs):
        v = (v * x + c) % p
    return v

def all_codewords_agreement(uvals, elts, k, s, p):
    """All distinct deg-<k codewords with |agreement| >= s, with their agreement index sets."""
    n = len(elts)
    idxs = list(range(n))
    seen = {}
    for T in itertools.combinations(idxs, k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = poly_coeffs(xs, ys, p)
        if c in seen: continue
        agree = frozenset(i for i in idxs if eval_poly(c, elts[i], p) == uvals[i])
        if len(agree) >= s:
            seen[c] = agree
    return seen

def is_symmetric(agree, neg):
    return all(neg[i] in agree for i in agree)

def even_word(elts, e_coeffs, p):
    """w(x) = w_e(x^2): an EVEN word from a level-1 poly e_coeffs evaluated at x^2."""
    return [eval_poly(e_coeffs, (x * x) % p, p) for x in elts]

def run(n, beta=4.0, rhos=(0.5, 0.25, 0.125, 0.0625)):
    print(f"\n========== n={n} (mu={n.bit_length()-1}) ==========")
    p = find_window_prime(n, beta)
    elts = subgroup(n, p)
    neg = neg_index_map(elts, p)
    n1 = n // 2
    elts1 = subgroup(n1, p)          # level-1 domain mu_{n/2} = {x^2}
    # consistency: squaring maps elts -> elts1 (as sets)
    sq = sorted(set((x * x) % p for x in elts))
    assert sq == sorted(elts1), "squaring image mismatch"
    print(f"  p={p}  level0 n={n}  level1 n/2={n1}")
    for rho in rhos:
        k = max(1, round(rho * n))
        if k >= n: continue
        eta = rho
        s = round((rho + eta) * n)
        if s < k: s = k
        if s > n: continue
        k1 = (k + 1) // 2     # ceil(k/2)
        s1 = (s + 1) // 2     # ceil(s/2)
        # pick an EVEN test word: w(x) = w_e(x^2) with a generic level-1 quadratic-ish e
        # use a couple of e's and report; the count is e-dependent but the IDENTITY is uniform.
        results = []
        for etag, ecoef in [("e=1+z", (1, 1)), ("e=1+z+z^2", (1, 1, 1)),
                            ("e=z", (0, 1)), ("e=z^2+z", (0, 1, 1))]:
            uv = even_word(elts, ecoef, p)
            # (A) brute symmetric count at level 0, restricted to EVEN codewords (f=0)
            seen = all_codewords_agreement(uv, elts, k, s, p)
            sym = {c: ag for c, ag in seen.items() if is_symmetric(ag, neg)}
            # even codewords: those whose poly has only even-degree terms (coeff odd = 0)
            even_cw = {c: ag for c, ag in sym.items()
                       if all(c[i] == 0 for i in range(1, len(c), 2))}
            L_sym = len(sym)
            L_even = len(even_cw)
            # (B) tower prediction: level-1 list of e against W=ecoef on mu_{n/2}, params (k1,s1)
            # the level-1 received word W = ecoef itself (w_e), agreement of level-1 polys
            W = [eval_poly(ecoef, z, p) for z in elts1]
            lvl1 = all_codewords_agreement(W, elts1, k1, s1, p)
            L_tower = len(lvl1)
            match = (L_even == L_tower)
            results.append((etag, L_sym, L_even, L_tower, match, k1, s1))
        print(f"    rho={rho:.4f} k={k} s={s}  ->  level1 (k1={k1}, s1={s1}):")
        for etag, Ls, Le, Lt, m, k1, s1 in results:
            print(f"        {etag:12s}: L_sym(all)={Ls:4d}  L_even(f=0)={Le:4d}  "
                  f"L_tower(lvl1)={Lt:4d}  even==tower? {m}")

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [8, 16, 32]
    for n in ns:
        run(n)
