#!/usr/bin/env python3
"""
probe_cr_matched_beta.py  (issue #444, [cr-monotonicity], MATCHED-beta extrapolation)

The regime probe showed a_r is HEAVILY p-dependent at small p (sumset width n^r > p
=> mod-p wraparound dominates). To extrapolate K_eff(n) honestly we must hold the regime
parameter fixed. Two regime-controlled experiments:

  EXP A (matched multiplier k): pick primes with p = k*n + 1 for the SAME small k across
  all n, so beta = log_n p = log_n(kn+1) ~ 1 + log_n k is as matched as the discrete prime
  constraint allows. Compare K_eff(n) at fixed r along this matched ridge.

  EXP B (large-p clean limit at fixed n): for n=16,32 push p as large as tractable
  (p ~ several thousand) so that p >> n^r for the shallow r we measure -- this is the
  regime that actually models the prize (beta>>1). Report the limiting a_r / K_eff and
  whether it has stabilized (two largest primes agree => that's the clean value).

This isolates: is the n-trend in K_eff an honest signal, or a p-artifact?
"""
from fractions import Fraction
from math import log

def is_prime(p):
    if p < 2: return False
    if p % 2 == 0: return p == 2
    i = 3
    while i*i <= p:
        if p % i == 0: return False
        i += 2
    return True

def prime_for_k(n, k):
    """Smallest prime p = k'*n+1 with k' >= k (proper)."""
    kk = max(2, k)
    while True:
        p = kk*n + 1
        if is_prime(p):
            return p
        kk += 1

def largest_prime_below(n, cap):
    """Largest prime p = k*n+1 <= cap."""
    best = None
    k = 2
    while k*n+1 <= cap:
        p = k*n+1
        if is_prime(p):
            best = p
        k += 1
    return best

def subgroup_mu_n(p, n):
    def order(a):
        o, x = 1, a % p
        while x != 1:
            x = (x*a) % p; o += 1
        return o
    g = next(c for c in range(2, p) if order(c) == p-1)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    assert len(S) == n
    return sorted(S)

def energy_exact(S, p, r):
    cur = [0]*p
    for a in S: cur[a % p] += 1
    for _ in range(r-1):
        nxt = [0]*p
        for v in range(p):
            cv = cur[v]
            if cv:
                for a in S:
                    nxt[(v+a) % p] += cv
        cur = nxt
    return sum(c*c for c in cur)

def dfodd(r):
    res = 1
    for k in range(1, r+1): res *= (2*k-1)
    return res

def ar_keff(S, p, n, r):
    E = energy_exact(S, p, r)
    Ar = Fraction(E) - Fraction(n**(2*r), p)
    Wick = dfodd(r)*(n**r)
    ar = Fraction(Ar, Wick)
    Keff = float(ar)**(1.0/r) if ar > 0 else float('nan')
    return float(ar), Keff

def main():
    print("=== EXP A: matched multiplier k (matched beta ridge) ===")
    print("For each k, p=k*n+1; compare K_eff(n) at fixed r.\n")
    ns = [16, 32, 64, 128]
    for k in [3, 4, 6]:
        print(f"-- multiplier k>={k} --")
        ps = {n: prime_for_k(n, k) for n in ns}
        for n in ns:
            print(f"   n={n}: p={ps[n]} (actual k={(ps[n]-1)//n}, beta={log(ps[n])/log(n):.3f})")
        Rmax = 4
        print(f"   {'r':>2} | " + " ".join(f"K_eff(n={n})" for n in ns))
        subs = {n: subgroup_mu_n(ps[n], n) for n in ns}
        for r in range(1, Rmax+1):
            vals = [ar_keff(subs[n], ps[n], n, r)[1] for n in ns]
            print(f"   {r:>2} | " + " ".join(f"{v:<10.4f}" for v in vals))
        print()

    print("\n=== EXP B: large-p clean limit at fixed n (does a_r stabilize?) ===")
    print("p pushed up so p >> n^r; if two largest primes agree, that's the clean value.\n")
    for n, cap, Rmax in [(16, 20000, 5), (32, 40000, 4)]:
        # take 4 increasing primes up to cap
        cands = []
        k = 2
        while k*n+1 <= cap:
            p = k*n+1
            if is_prime(p):
                cands.append(p)
            k += 1
        # sample: smallest, ~1/3, ~2/3, largest
        idx = sorted(set([0, len(cands)//3, 2*len(cands)//3, len(cands)-1]))
        ps = [cands[i] for i in idx]
        print(f"-- n={n}, primes {ps} (betas {[round(log(p)/log(n),3) for p in ps]}) --")
        subs = {p: subgroup_mu_n(p, n) for p in ps}
        print(f"   {'r':>2} | " + " ".join(f"a_r@p={p:<7}" for p in ps) + " | clean K_eff@maxp")
        for r in range(1, Rmax+1):
            row = [ar_keff(subs[p], p, n, r) for p in ps]
            ars = [x[0] for x in row]
            print(f"   {r:>2} | " + " ".join(f"{a:<10.5f}" for a in ars) +
                  f" | {row[-1][1]:.5f}")
        print()

if __name__ == "__main__":
    main()
