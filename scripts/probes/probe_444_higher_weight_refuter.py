#!/usr/bin/env python3
"""
probe_444_higher_weight_refuter.py  (#444 SEAM A -- Refuter A: higher-weight break)

GOAL (refutation attempt): the descent/monomial-constancy path ASSUMES the worst-case
window word is LOW WEIGHT (weight 2). Test this by scanning weight-3 (full) and a sample
of weight-4 words on mu_n at n=16 and n=32, over multiple prize-shaped primes, at the
window interior, and find the TRUE worst-case window list over ALL words up to weight 4.

If any higher-weight word gives a STRICTLY larger or n-GROWING window list than the
weight-2 worst, the path is REFUTED.

Conventions (honesty): exact arithmetic mod p, multiple primes, proper subgroup mu_n
(m=(p-1)/n > 1, never n=p-1), window-interior radius s=(rho+eta)n, exclude correlated
directions whose exponent set is supported on x^{n/2}=+-1.

Word model: w(x) = sum_t c_t x^{e_t}, exponents e_t in [0,n), distinct, weight = #terms.
We scan c_t = 1 (the canonical structured words named in the path) AND a sample of general
nonzero coefficient vectors (to make sure the "all-ones" choice is not hiding a larger list).
"""
import itertools, sys, random
from math import comb
from sympy import isprime, primitive_root

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
    assert len(set(elts)) == n, "subgroup degenerate"
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
    """# distinct deg<k polys agreeing with u on >= s pts of mu_n (exact full enumeration)."""
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
    """exclude 'correlated direction' words: all exponents == n/2 mod n (x^{n/2}=+-1 fiber).
       We exclude any word whose exponent SET, reduced mod n, lies entirely in {0, n/2}
       (those are constant/+-1 combinations -- degenerate near-codewords)."""
    h = n // 2
    return all((e % n) in (0, h) for e in exps)

def scan_weight(n, k, eta, weight, beta, primes_betas, coeff_modes, exp_cap=None,
                sample_exps=None, seed=0):
    """For each prime, find worst window list over weight-`weight` words.
       Returns: dict prime -> (bestL, best_exps, best_coeffs, s)."""
    rng = random.Random(seed)
    out = {}
    for pb in primes_betas:
        p = find_window_prime(n, pb)
        if p in out:  # same prime from different beta; skip dup
            continue
        elts = subgroup(n, p)
        rho = k / n
        s = round((rho + eta) * n); s = max(s, k); s = min(s, n)
        # exponent tuples to scan
        maxexp = n if exp_cap is None else min(n, exp_cap)
        if sample_exps is None:
            exp_iter = itertools.combinations(range(1, maxexp), weight)
        else:
            exp_iter = sample_exps
        best = (-1, None, None)
        for exps in exp_iter:
            exps = tuple(exps)
            if is_correlated(exps, n):
                continue
            for mode in coeff_modes:
                if mode == "ones":
                    coeffs = (1,) * weight
                    uv = word_vals(elts, exps, coeffs, p)
                    L = list_RS(uv, elts, k, s, p)
                    if L > best[0]: best = (L, exps, coeffs)
                elif mode == "random":
                    for _ in range(coeff_modes_count):
                        coeffs = tuple(rng.randrange(1, p) for _ in range(weight))
                        uv = word_vals(elts, exps, coeffs, p)
                        L = list_RS(uv, elts, k, s, p)
                        if L > best[0]: best = (L, exps, coeffs)
        out[p] = (best[0], best[1], best[2], s)
    return out

coeff_modes_count = 3  # random coeff vectors per exponent tuple when mode=="random"

def fmt(res):
    lines = []
    for p, (L, exps, coeffs, s) in sorted(res.items()):
        cdesc = "ones" if coeffs == (1,) * len(coeffs) else f"coeffs={coeffs}"
        lines.append(f"      p={p} s={s}: L={L}  exps={exps} {cdesc}")
    return "\n".join(lines)

def run():
    # window-interior settings matched to the prompt's weight-2 baselines:
    #   n=16 rho=1/8 (k=2) -> weight-2 worst L=4 ;  rho=1/16 (k=1) -> L=7
    # use eta = rho (dossier midpoint) so s=(rho+eta)n = 2*k.
    # For n=32 the analogous rates rho=1/8 (k=4) is too big to fully enumerate weight-3
    #   over all exponents AND all 8-subsets; we use rho=1/16 (k=2, s=4) which is enumerable,
    #   plus rho=1/8 with a capped-exponent / sampled scan.
    configs = []
    # (n, k, eta, label)
    configs.append((16, 2, 0.125, "n16_rho1/8"))    # weight-2 baseline L=4
    configs.append((16, 1, 0.0625, "n16_rho1/16"))  # weight-2 baseline L=7
    configs.append((32, 2, 0.0625, "n32_rho1/16"))  # k=2 enumerable fully
    configs.append((32, 1, 0.03125, "n32_rho1/32")) # k=1, deepest

    primes_betas = [4.0, 4.4]  # two structurally different prize-shaped primes (beta~4)

    for (n, k, eta, label) in configs:
        rho = k / n
        s = round((rho + eta) * n)
        print(f"\n########## {label}: n={n} k={k} rho={rho:.4f} eta={eta} s={max(s,k)} ##########")
        ck = comb(n, k)
        print(f"  (C(n,k)={ck} k-subsets per word)")

        # ---- weight 2 (reproduce baseline) ----
        r2 = scan_weight(n, k, eta, 2, 4.0, primes_betas, ["ones"])
        print(f"  WEIGHT-2 (ones, full exp scan):")
        print(fmt(r2))
        # also random coeffs for weight-2 to confirm ones is worst-ish
        r2r = scan_weight(n, k, eta, 2, 4.0, primes_betas, ["ones", "random"], seed=11)
        print(f"  WEIGHT-2 (ones+random coeffs):")
        print(fmt(r2r))

        # ---- weight 3 (FULL exponent scan, ones) ----
        # number of weight-3 exp tuples ~ C(n-1,3); each needs C(n,k) interpolations.
        r3 = scan_weight(n, k, eta, 3, 4.0, primes_betas, ["ones"])
        print(f"  WEIGHT-3 (ones, full exp scan):")
        print(fmt(r3))
        # weight-3 with random coeffs (sample of exponent tuples to bound cost)
        all3 = list(itertools.combinations(range(1, n), 3))
        rng = random.Random(7)
        samp3 = all3 if len(all3) <= 80 else rng.sample(all3, 80)
        r3r = scan_weight(n, k, eta, 3, 4.0, primes_betas, ["ones", "random"],
                          sample_exps=samp3, seed=23)
        print(f"  WEIGHT-3 (ones+random coeffs, {len(samp3)} exp tuples):")
        print(fmt(r3r))

        # ---- weight 4 (SAMPLE of exponent tuples, ones + random) ----
        all4 = list(itertools.combinations(range(1, n), 4))
        rng = random.Random(13)
        samp4 = all4 if len(all4) <= 120 else rng.sample(all4, 120)
        r4 = scan_weight(n, k, eta, 4, 4.0, primes_betas, ["ones", "random"],
                         sample_exps=samp4, seed=31)
        print(f"  WEIGHT-4 (ones+random coeffs, {len(samp4)}/{len(all4)} exp tuples sampled):")
        print(fmt(r4))

if __name__ == "__main__":
    run()
