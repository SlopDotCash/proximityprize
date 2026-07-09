#!/usr/bin/env python3
"""
probe_444_attacker_maxc_fast.py  (#444 ATTACKER, fast & decisive)

For each (n, prime p), find the MAX c over ALL size-s subsets such that a NON-coset, NON-antipodal-
balanced defect has p_1..p_c == 0 mod p. Then test the refutation condition  c/n > log(s)/(2 log p)
i.e.  p > s^{n/(2c)}.

Efficiency: we DON'T classify cosets up front; instead we directly enumerate subsets and, for each
that is lacunary to depth c, check it's a genuine defect (not a 2-power coset union, not antipodal-
balanced). We track the global max (c, with the largest eta - eta_crit margin).

We sweep:
  - n=32, s in a useful range, MANY primes (small AND large), find largest-c defect + margin.
  - n=64, s small, c=2..., a few primes (expensive; only c<=3 reachable).
The goal: does ANY defect ever satisfy eta > eta_crit? If yes => REFUTED.
"""
import itertools, math
from math import comb, log
from sympy import isprime, primitive_root

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e = []; x = 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e

def two_power_cosets(n):
    """dict tau -> list of frozenset cosets of mu_tau (tau 2-power | n)."""
    res = {}
    taus = [t for t in range(1, n+1) if n % t == 0 and (t & (t-1)) == 0]
    for tau in taus:
        step = n // tau
        seen = set(); cosets = []
        for i0 in range(step):
            c = frozenset((i0 + step*j) % n for j in range(tau))
            if c not in seen:
                seen.add(c); cosets.append(c)
        res[tau] = cosets
    return res

def coset_unions_of_size(cosets_by_tau, n, s):
    out = set()
    for tau, cosets in cosets_by_tau.items():
        if s % tau != 0:
            continue
        need = s // tau
        if need > len(cosets):
            continue
        for combo in itertools.combinations(cosets, need):
            U = frozenset().union(*combo)
            if len(U) == s:
                out.add(U)
    return out

def is_balanced(n, idxs):
    half = n//2; ss = set(idxs)
    return all(((i+half) % n) in ss for i in idxs)

def scan_n_p(n, p, s_range, cosets_by_tau):
    """Return (best_margin, best_info) over all size-s defects, s in s_range."""
    elts = subgroup(n, p)
    best = (-9.9, None)
    for s in s_range:
        if comb(n, s) > 2_500_000:
            continue
        cosets = coset_unions_of_size(cosets_by_tau, n, s)
        powtab = [[pow(v, j, p) for j in range(1, s+1)] for v in elts]
        for combo in itertools.combinations(range(n), s):
            # depth of vanishing
            c = 0
            for j in range(1, s+1):
                t = 0
                for i in combo:
                    t += powtab[i][j-1]
                if t % p == 0:
                    c += 1
                else:
                    break
            if c == 0:
                continue
            T = frozenset(combo)
            if T in cosets or is_balanced(n, combo):
                continue
            eta = c / n
            eta_crit = log(s) / (2*log(p))
            margin = eta - eta_crit
            if margin > best[0]:
                best = (margin, (s, c, p, eta, eta_crit, combo))
    return best

if __name__ == "__main__":
    print("### ATTACKER fast max-c defect: REFUTE iff any defect has eta=c/n > log(s)/(2 log p) ###\n")
    # ---- n=32 ----
    n = 32
    cbt = two_power_cosets(n)
    primes = []
    pp = n+1
    while len(primes) < 60:
        if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= 2:
            primes.append(pp)
        pp += n
    # also add some larger primes (p ~ n^2, n^3) to shrink eta_crit
    for beta in [2.0, 2.5, 3.0, 3.5, 4.0]:
        t = int(n**beta); base = t - (t % n) + 1; q = base
        while True:
            if isprime(q) and (q-1) % n == 0 and (q-1)//n >= 2:
                primes.append(q); break
            q += n
    print(f"--- n={n}: {len(primes)} primes from {primes[0]} to {max(primes)} ---", flush=True)
    s_range = list(range(4, 11))  # comb(32,10)=64M too big; auto-skipped above. 4..9 used.
    overall = (-9.9, None)
    refuters = []
    for p in primes:
        m, info = scan_n_p(n, p, s_range, cbt)
        if info is None:
            continue
        if m > overall[0]:
            overall = (m, info)
        if m > 0:
            refuters.append(info)
    if overall[1]:
        s, c, p, eta, ec, combo = overall[1]
        print(f"  BEST defect margin = {overall[0]:+.4f}  at p={p} s={s} c={c} eta={eta:.4f} "
              f"eta_crit={ec:.4f}  T={list(combo)}", flush=True)
    print(f"  REFUTERS (eta>eta_crit): {len(refuters)}", flush=True)
    for info in refuters[:10]:
        s, c, p, eta, ec, combo = info
        print(f"     !!! p={p} s={s} c={c} eta={eta:.4f} > eta_crit={ec:.4f}  T={list(combo)}", flush=True)

    # ---- n=64, small s, find any defect and its max c ----
    n = 64
    cbt = two_power_cosets(n)
    primes64 = []
    pp = n+1
    while len(primes64) < 25:
        if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= 2:
            primes64.append(pp)
        pp += n
    print(f"\n--- n={n}: {len(primes64)} primes from {primes64[0]} to {max(primes64)} ---", flush=True)
    s_range = [6, 8, 10]  # comb(64,10)=151M too big -> auto-skip; comb(64,8)=4.4G skip; comb(64,6)=74M skip
    # only comb(64,6)=74M is too big. Use s in [6] won't run. Use s up to where comb<=2.5M: comb(64,4)=635k, comb(64,5)=7.6M(skip), comb(64,6) skip.
    s_range = [4, 5]
    overall = (-9.9, None); refuters = []
    for p in primes64:
        m, info = scan_n_p(n, p, s_range, cbt)
        if info is None:
            continue
        if m > overall[0]:
            overall = (m, info)
        if m > 0:
            refuters.append(info)
    if overall[1]:
        s, c, p, eta, ec, combo = overall[1]
        print(f"  BEST defect margin = {overall[0]:+.4f}  at p={p} s={s} c={c} eta={eta:.4f} "
              f"eta_crit={ec:.4f}  T={list(combo)}", flush=True)
    else:
        print("  no defect found in accessible (s<=5) range at n=64", flush=True)
    print(f"  REFUTERS (eta>eta_crit): {len(refuters)}", flush=True)
    for info in refuters[:10]:
        s, c, p, eta, ec, combo = info
        print(f"     !!! p={p} s={s} c={c} eta={eta:.4f} > eta_crit={ec:.4f}  T={list(combo)}", flush=True)
