#!/usr/bin/env python3
"""
probe_444_adversary_g2_growth.py  -- isolate the n-growth signal found by probe_444_adversary_g2.

The main probe found weight-2 stays worst (G2 clause-1 survives) but worst-L GROWS:
  k=1 family: n=16 L=8 -> n=32 L=16 ;  k=2 family: n=16 L=4 -> n=32 L=8.
But there k and rho both moved (eta=rho => s=2k, rho=k/n shrinks with n). This control
disambiguates by holding things fixed:

  A. eta=rho (prompt convention, s=2k FIXED, rho=k/n SHRINKS): scan worst weight-2 L over
     n in {16,32,64}, fixed k. If L doubles with n, the worst-case list is UNBOUNDED in n.
  B. fixed ABSOLUTE rho=1/4 (k=n/4), eta=rho so s=round(n/2). worst weight-2 L vs n.
  C. fixed ABSOLUTE rho=1/8 (k=n/8), eta=rho so s=round(n/4). worst weight-2 L vs n.

Decoder substrate copied verbatim from probe_444_adversary_g2 (exact, multi-prime).
"""
import itertools
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
    assert len(set(elts)) == n
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
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = (den * ((xs[i] - xs[j]) % p)) % p
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


def is_correlated(exps, n):
    h = n // 2
    return all((e % n) in (0, h) for e in exps)


def worst_weight2(n, k, s, p, elts):
    best = (-1, None)
    for a in range(1, n):
        for b in range(0, a):
            if is_correlated((a, b), n):
                continue
            uv = word_vals(elts, (a, b), (1, 1), p)
            L = list_RS(uv, elts, k, s, p)
            if L > best[0]:
                best = (L, (a, b))
    return best


from math import comb

# feasibility guard: skip full weight-2 scan if it would do too many interpolations.
# cost ~ (#weight-2 words ~ n^2/2) * C(n,k).  Cap at ~2e8 interp evaluations.
COST_CAP = 2e8


def feasible(n, k):
    return (n * n / 2) * comb(n, k) <= COST_CAP


def run():
    print("=== CONTROL A: eta=rho (s=2k FIXED, rho=k/n shrinks), worst weight-2 L vs n ===")
    print("    [k FIXED, n grows -> if L doubles, worst-case window list is UNBOUNDED in n]")
    for k in (1, 2):
        print(f"  -- k={k} (s=2k={2*k}) --")
        for n in (16, 32, 64, 128):
            if not feasible(n, k):
                print(f"     n={n:>3} k={k}: SKIP (infeasible full scan)"); continue
            s = max(min(2 * k, n), k)
            for beta in (4.0, 4.4):
                p = find_window_prime(n, beta)
                elts = subgroup(n, p)
                L, e = worst_weight2(n, k, s, p, elts)
                print(f"     n={n:>3} rho={k/n:.6f} s={s} p={p}: worst-w2 L={L} exps={e}")

    print("\n=== CONTROL B: fixed absolute rho=1/4 (k=n/4), eta=rho => s=round(n/2). worst w2 L vs n ===")
    print("    [TRUE fixed-rate regime the prize cares about]")
    for n in (16, 32, 64):
        k = n // 4
        if not feasible(n, k):
            print(f"  n={n:>2} k={k}: SKIP (infeasible full scan, C(n,k)={comb(n,k)})"); continue
        rho = k / n; eta = rho
        s = max(min(round((rho + eta) * n), n), k)
        for beta in (4.0, 4.4):
            p = find_window_prime(n, beta)
            elts = subgroup(n, p)
            L, e = worst_weight2(n, k, s, p, elts)
            print(f"  n={n:>2} k={k} rho={rho:.4f} s={s} p={p}: worst-w2 L={L} exps={e}")

    print("\n=== CONTROL C: fixed absolute rho=1/8 (k=n/8), eta=rho => s=round(n/4). worst w2 L vs n ===")
    for n in (16, 32, 64):
        k = n // 8
        if k < 1: continue
        if not feasible(n, k):
            print(f"  n={n:>2} k={k}: SKIP (infeasible full scan, C(n,k)={comb(n,k)})"); continue
        rho = k / n; eta = rho
        s = max(min(round((rho + eta) * n), n), k)
        p = find_window_prime(n, 4.0)
        elts = subgroup(n, p)
        L, e = worst_weight2(n, k, s, p, elts)
        print(f"  n={n:>2} k={k} rho={rho:.4f} s={s} p={p}: worst-w2 L={L} exps={e}")


if __name__ == "__main__":
    run()
