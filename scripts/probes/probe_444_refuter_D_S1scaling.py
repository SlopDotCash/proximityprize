#!/usr/bin/env python3
"""
probe_444_refuter_D_S1scaling.py   (#444 SEAM A -- REFUTER D, decisive S_1 scaling test)

Directly answers: does the single-fiber term |S_1| = #{y in mu_N : Q!=0, P^2 = y Q^2} SCALE
WITH n for the worst weight-2 word, at FIXED rho=k/n, as eta is lowered toward Johnson?

Method: for each (n, k), sweep agreement threshold s downward; over ALL weight-2 words
x^a+x^b (a,b != n/2, a!=b) and ALL their list members f (deg<k agreeing on >= s pts),
compute the even/odd split P=F-u_e, Q=G-u_o and the ACTUAL |S_1| on mu_N. Report:
  - the global max |S_1| over all words & members at that s,
  - the max deg(P^2 - X Q^2),
  - the word/member achieving the max.
Then compare across n=16,32,64 at matched rho and matched 'window depth' (s - johnson-ish).
REFUTE if max|S_1| grows with n at fixed rho; SUPPORT if it stays O(k) (bounded).
"""
import itertools, sys
from math import comb, isqrt
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta); base = target - (target % n) + 1; p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min: return p
        p += n

def subgroup(n, p):
    g = primitive_root(p); zeta = pow(g, (p - 1) // n, p)
    e, x = [], 1
    for _ in range(n): e.append(x); x = (x * zeta) % p
    assert len(set(e)) == n
    return e

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b): r[i + j] = (r[i + j] + ai * bj) % p
    return r

def poly_trim(c):
    c = list(c)
    while len(c) > 1 and c[-1] == 0: c.pop()
    return c

def poly_deg(c):
    c = poly_trim(c)
    return -1 if (len(c) == 1 and c[0] == 0) else len(c) - 1

def poly_sub(a, b, p):
    n = max(len(a), len(b)); r = [0] * n
    for i in range(len(a)): r[i] = (r[i] + a[i]) % p
    for i in range(len(b)): r[i] = (r[i] - b[i]) % p
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

def list_with_agree(uvals, elts, k, s, p):
    n = len(elts); seen = {}
    for T in itertools.combinations(range(n), k):
        c = interp_coeffs([elts[i] for i in T], [uvals[i] for i in T], p)
        if c in seen: continue
        ag = sum(1 for i in range(n) if peval(c, elts[i], p) == uvals[i])
        seen[c] = ag
    return [(c, a) for c, a in seen.items() if a >= s]

def split_even_odd(coeffs):
    F = poly_trim([coeffs[i] for i in range(0, len(coeffs), 2)] or [0])
    G = poly_trim([coeffs[i] for i in range(1, len(coeffs), 2)] or [0])
    return F, G

def word_split_even_odd(a, b, N, p):
    ue = [0] * N; uo = [0] * N
    for c in (a, b):
        if c % 2 == 0: ue[(c // 2) % N] = (ue[(c // 2) % N] + 1) % p
        else:          uo[((c - 1) // 2) % N] = (uo[((c - 1) // 2) % N] + 1) % p
    return poly_trim(ue), poly_trim(uo)

def max_S1_over_words(n, k, s, p):
    """global max |S_1| over all weight-2 words and all list members."""
    elts = subgroup(n, p)
    eltsN = sorted({(x * x) % p for x in elts})
    N = n // 2
    best = (-1, None, None, -1)  # (|S_1|, (a,b), agree, degR)
    Lmax = 0
    for a in range(0, n):
        for b in range(0, a):
            if a == n // 2 or b == n // 2: continue
            u = [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]
            lst = list_with_agree(u, elts, k, s, p)
            Lmax = max(Lmax, len(lst))
            ue, uo = word_split_even_odd(a, b, N, p)
            for (c, agree) in lst:
                F, G = split_even_odd(c)
                P = poly_sub(F, ue, p); Q = poly_sub(G, uo, p)
                s1 = 0; common = 0
                for y in eltsN:
                    Pv = peval(P, y, p); Qv = peval(Q, y, p)
                    if Pv == 0 and Qv == 0: common += 1
                    elif Qv != 0 and (Pv * Pv - y * Qv * Qv) % p == 0: s1 += 1
                assert 2 * common + s1 == agree, f"IDENTITY FAIL {agree} {common} {s1}"
                if s1 > best[0]:
                    R = poly_sub(poly_mul(P, P, p), poly_mul([0, 1], poly_mul(Q, Q, p), p), p)
                    best = (s1, (a, b), agree, poly_deg(R))
    return best, Lmax, N

if __name__ == "__main__":
    print("### DECISIVE: max |S_1| over ALL weight-2 words, sweeping s down, vs n ###")
    print("    (rho=k/n fixed; lower s = closer to Johnson = larger lists = S_1 fires)")
    for k in [2]:
        print(f"\n  --- k={k} ---")
        for n in [16, 32, 64]:
            p = find_window_prime(n, 4.0)
            rho = k / n
            # sweep s from generous window down to just above k
            row = []
            johnson = isqrt(k * n) + 1  # rough Johnson-ish agreement floor sqrt(k n)
            for s in range(max(k + 1, johnson - 2), n):
                if comb(n, k) > 1_500_000: break
                (best, Lmax, N) = max_S1_over_words(n, k, s, p)
                row.append((s, best[0], Lmax, best[1], best[3]))
            print(f"    n={n:3d}(N={N}) rho={rho:.3f} p={p} johnson~{johnson}:")
            for (s, s1, Lmax, ab, degR) in row:
                eta = s / n - rho
                print(f"        s={s:2d}(eta={eta:+.3f}) Lmax={Lmax:3d}  max|S_1|={s1:2d}  "
                      f"at x^{ab[0]}+x^{ab[1]}  degR={degR}")
