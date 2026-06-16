#!/usr/bin/env python3
"""
probe_444_refuter_D_v2.py   (#444 SEAM A -- REFUTER D, refined)

Refined: proper WINDOW-INTERIOR radius (eta = 0.25 default, the campaign's verified value,
so the worst-word list is genuinely SMALL, not a near-MDS explosion), faster weight-2-only
search, explicit scaling report of (deg P, deg Q, deg(P^2 - X Q^2), |S_1|) vs n at fixed rho.

Two jobs (see header of probe_444_refuter_D_singlefiber.py for full statement):
  JOB 1: for the TRUE worst weight-2 word x^a+x^b on mu_n at window-interior radius, every list
         member f splits f=F(x^2)+xG(x^2); P=F-u_e, Q=G-u_o; agreement
            |S| = 2 #{P=Q=0} + |S_1|,  S_1 = {y in mu_N: Q!=0, P^2 = y Q^2}.
         Report max|S_1| and max deg(P^2 - X Q^2). CLAIM: |S_1| = O(k) (REFUTE if ~ n).
  JOB 2: descent recursion: same parity -> 2-term child on mu_{n/2}; mixed -> monomial pair;
         same-parity run length == v2(a-b).  Verified symbolically over all (n,a,b).
"""
import itertools, sys
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

def full_list(uvals, elts, k, s, p):
    n = len(elts); seen = {}
    for T in itertools.combinations(range(n), k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = interp_coeffs(xs, ys, p)
        if c in seen: continue
        ag = sum(1 for i in range(n) if peval(c, elts[i], p) == uvals[i])
        seen[c] = ag
    return [(c, a) for c, a in seen.items() if a >= s]

def true_worst_weight2(n, k, s, p):
    elts = subgroup(n, p)
    best = (-1, None, None)
    for a in range(0, n):
        for b in range(0, a):
            if a == n // 2 or b == n // 2: continue   # exclude correlated x^{n/2}=+-1
            u = [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]
            lst = full_list(u, elts, k, s, p)
            if len(lst) > best[0]: best = (len(lst), (a, b), lst)
    return best, elts

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

def job1(n, k, eta, beta=4.0):
    N = n // 2
    p = find_window_prime(n, beta)
    rho = k / n
    s = round((rho + eta) * n); s = max(s, k + 1); s = min(s, n)
    (L, ab, lst), elts = true_worst_weight2(n, k, s, p)
    a, b = ab
    eltsN = sorted({(x * x) % p for x in elts})
    assert len(eltsN) == N
    ue, uo = word_split_even_odd(a, b, N, p)
    deg_ue, deg_uo = poly_deg(ue), poly_deg(uo)
    max_S1 = -1; max_deg = -1; max_dP = -1; max_dQ = -1
    s1vals = set(); degvals = set()
    for (c, agree) in lst:
        F, G = split_even_odd(c)
        P = poly_sub(F, ue, p); Q = poly_sub(G, uo, p)
        R = poly_sub(poly_mul(P, P, p), poly_mul([0, 1], poly_mul(Q, Q, p), p), p)
        dR = poly_deg(R)
        s1 = 0; common = 0
        for y in eltsN:
            Pv = peval(P, y, p); Qv = peval(Q, y, p)
            if Pv == 0 and Qv == 0: common += 1
            elif Qv != 0 and (Pv * Pv - y * Qv * Qv) % p == 0: s1 += 1
        assert 2 * common + s1 == agree, f"IDENTITY FAIL agree={agree} 2*{common}+{s1}"
        max_S1 = max(max_S1, s1); max_deg = max(max_deg, dR)
        max_dP = max(max_dP, poly_deg(P)); max_dQ = max(max_dQ, poly_deg(Q))
        s1vals.add(s1); degvals.add(dR)
    print(f"  n={n:3d}(N={N}) k={k} rho={rho:.3f} eta={eta} s={s} p={p}  "
          f"worst x^{a}+x^{b}  L={L}")
    print(f"        deg u_e={deg_ue} deg u_o={deg_uo} | max deg P={max_dP} max deg Q={max_dQ} | "
          f"max deg(P^2-X Q^2)={max_deg} | max|S_1|={max_S1}  (k={k}, N={N})")
    print(f"        |S_1| seen={sorted(s1vals)}  deg(R) seen={sorted(degvals)}")
    return dict(n=n, k=k, rho=rho, L=L, worst=(a, b), max_S1=max_S1, max_deg=max_deg,
                max_dP=max_dP, max_dQ=max_dQ, N=N)

def v2(m):
    m = abs(m)
    if m == 0: return None
    c = 0
    while m % 2 == 0: m //= 2; c += 1
    return c

def descend_word(a, b, n):
    N = n // 2; pa, pb = a % 2, b % 2
    if pa == pb:
        if pa == 0: return ('same-even', (a // 2 % N, b // 2 % N))
        else:       return ('same-odd', ((a - 1) // 2 % N, (b - 1) // 2 % N))
    else:
        if pa == 0: return ('mixed', (a // 2 % N, (b - 1) // 2 % N))
        else:       return ('mixed', (b // 2 % N, (a - 1) // 2 % N))

def job2_symbolic():
    print("\n### JOB 2: descent recursion structure (symbolic, exhaustive) ###")
    ok_depth = True; ok_struct = True; bad = []
    for n in [16, 32, 64, 128, 256]:
        for a in range(1, n):
            for b in range(0, a):
                depth_pred = v2(a - b)
                ca, cb, cn, level, term = a, b, n, 0, None
                while cn >= 2:
                    kind, child = descend_word(ca, cb, cn)
                    if kind == 'mixed':
                        term = level; break
                    # structural check: same parity must give a genuine 2-term word (a'!=b')
                    if child[0] == child[1]:
                        # collision: a/2 == b/2 mod N can happen if a-b == n/2 ... record
                        ok_struct = False; bad.append((n, a, b, cn, 'child-collision', child))
                    ca, cb = child; cn //= 2; level += 1
                    if cn < 2: term = None; break
                if term is not None and term != depth_pred:
                    ok_depth = False; bad.append((n, a, b, 'depth', term, depth_pred))
    print(f"   same-parity run length == v2(a-b) for ALL (n,a,b): {ok_depth}")
    print(f"   same-parity child is a genuine 2-term word (no collision): {ok_struct}")
    if bad:
        for x in bad[:10]: print(f"      anomaly: {x}")
    return ok_depth, ok_struct

if __name__ == "__main__":
    print("### JOB 1: single-fiber |S_1| scaling, window-interior radius (eta=0.25) ###")
    res = []
    for (n, k, eta) in [(16, 2, 0.25), (32, 2, 0.25), (64, 2, 0.25),
                        (16, 4, 0.25), (32, 4, 0.25)]:
        if comb(n, k) > 1_500_000:
            print(f"  n={n} k={k}: SKIP C={comb(n,k)}"); continue
        res.append(job1(n, k, eta))
    print("\n  [SCALING at fixed rho=k/n]:")
    for rho_t in sorted({r['rho'] for r in res}):
        row = [r for r in res if abs(r['rho'] - rho_t) < 1e-9]
        row.sort(key=lambda r: r['n'])
        seq = ", ".join(f"n={r['n']}:|S1|={r['max_S1']}(degR={r['max_deg']})" for r in row)
        print(f"    rho={rho_t:.3f}:  {seq}")
    job2_symbolic()
