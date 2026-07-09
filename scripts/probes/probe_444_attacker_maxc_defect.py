#!/usr/bin/env python3
"""
probe_444_attacker_maxc_defect.py  (#444 ATTACKER, decisive)

The floor claims: NO non-coset defect exists with eta > eta_crit = log(s)/(2 log p), where
eta = c/n (c = #vanishing power sums), s = |S|.

So a defect REFUTES the floor iff   c/n  >  log(s)/(2 log p),  equivalently
   p  >  s^{n/(2c)}   (== the norm ceiling being VIOLATED by an actual defect).

Strategy to MAXIMIZE chance of refutation:
  - For each (n, s), find the LARGEST c such that SOME non-coset defect (non-antipodal-balanced,
    and also NOT a deep-coset-union) exists with first c power sums vanishing, over a prime sweep.
  - Report eta = c/n, eta_crit = log(s)/(2 log p) at the defect prime, and verdict eta>eta_crit.
  - Also separately: for a FIXED eta target (large), sweep primes p UPWARD (so eta_crit shrinks)
    and check if the defect SURVIVES to a prime where eta_crit < eta.

We classify a lacunary S as DEFECT iff it is NOT a union of mu_tau-cosets (char-0 structure).
This is the exact object the floor says vanishes above eta_crit.
"""
import itertools, math, cmath
from math import comb, log
from sympy import isprime, primitive_root

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e = []; x = 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e

def two_power_coset_unions(n, s):
    """All index-subsets of size s that are unions of mu_tau cosets (tau a 2-power | n)."""
    out = set()
    taus = [t for t in range(1, n+1) if n % t == 0 and (t & (t-1)) == 0]
    for tau in taus:
        if s % tau != 0:
            continue
        step = n // tau
        cosets = []
        seen = set()
        for i0 in range(step):
            c = frozenset((i0 + step*j) % n for j in range(tau))
            if c not in seen:
                seen.add(c); cosets.append(c)
        need = s // tau
        if need > len(cosets):
            continue
        for combo in itertools.combinations(cosets, need):
            U = frozenset().union(*combo)
            if len(U) == s:
                out.add(U)
    return out

def max_c_defect(n, p, s):
    """For subgroup mu_n mod p, find the max c such that a NON-COSET-UNION size-s subset has
       p_1..p_c == 0 mod p. Returns (max_c, witness_idx) or (0, None) if no non-coset lacunary
       with c>=1 (c>=1 always trivially achievable? sum=0 needed). We require c>=1."""
    elts = subgroup(n, p)
    coset_unions = two_power_coset_unions(n, s)
    powtab = [[pow(v, j, p) for j in range(0, s+1)] for v in elts]  # x^0..x^s
    best_c = 0; best_T = None
    for combo in itertools.combinations(range(n), s):
        # compute how many leading power sums vanish
        c = 0
        for j in range(1, s+1):
            t = 0
            for i in combo:
                t += powtab[i][j]
            if t % p == 0:
                c += 1
            else:
                break
        if c == 0:
            continue
        T = frozenset(combo)
        if T in coset_unions:
            continue  # char-0 structure, not a defect
        if c > best_c:
            best_c = c; best_T = combo
    return best_c, best_T

def beta_abs(idxs, n):
    z = 2j*math.pi/n
    return abs(sum(cmath.exp(z*i) for i in idxs))

def is_antipodal_free(idxs, n):
    half = n//2; ss = set(idxs)
    return not any(((i+half) % n) in ss for i in idxs)

def primes_1_mod_n(n, count, idx_min=2, pmin=None):
    out = []; pp = (pmin or n)
    pp = pp - (pp % n) + 1
    if pp <= n:
        pp = n + 1
    while len(out) < count:
        if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= idx_min:
            out.append(pp)
        pp += n
    return out

def run(n, s_list, nprimes=120):
    print(f"\n{'='*92}\n### MAX-c DEFECT SCAN  n={n}  (REFUTE iff a defect has eta=c/n > log(s)/(2 log p)) ###\n{'='*92}", flush=True)
    refutations = 0
    for s in s_list:
        if comb(n, s) > 4_000_000:
            print(f"  s={s}: comb too large, skip", flush=True)
            continue
        primes = primes_1_mod_n(n, nprimes, idx_min=2, pmin=n)
        global_best = (0, None, None)  # (eta - eta_crit, info, ...)
        best_above = None
        max_c_seen = 0
        for p in primes:
            c, T = max_c_defect(n, p, s)
            if c == 0:
                continue
            max_c_seen = max(max_c_seen, c)
            eta = c / n
            eta_crit = log(s) / (2*log(p))
            margin = eta - eta_crit
            if margin > global_best[0]:
                global_best = (margin, (p, c, T, eta, eta_crit))
            if margin > 0:  # REFUTATION
                if best_above is None:
                    best_above = (p, c, T, eta, eta_crit, margin)
        # report
        m, info = global_best[0], global_best[1]
        if info is None:
            print(f"  s={s}: NO non-coset defect found over {nprimes} primes.", flush=True)
            continue
        p, c, T, eta, eta_crit = info
        af = is_antipodal_free(T, n); b = beta_abs(T, n)
        status = ">>> REFUTES FLOOR <<<" if m > 0 else "(below eta_crit, floor holds)"
        print(f"  s={s}: best margin={m:+.4f} at p={p} c={c} eta={eta:.4f} eta_crit={eta_crit:.4f} "
              f"max_c_seen={max_c_seen} af={af} |b|={b:.3f} ex={list(T)} {status}", flush=True)
        if best_above is not None:
            refutations += 1
            p, c, T, eta, eta_crit, margin = best_above
            print(f"      REFUTING DEFECT: p={p} c={c} s={s} eta={eta:.4f} > eta_crit={eta_crit:.4f} "
                  f"(margin {margin:+.4f})  T={list(T)}", flush=True)
    return refutations

if __name__ == "__main__":
    print("ATTACKER MAX-c DEFECT SCAN: find the deepest (largest-c) non-coset defect per (n,s),")
    print("then test whether its eta=c/n exceeds eta_crit=log(s)/(2 log p).")
    total = 0
    total += run(16, [4, 5, 6, 7, 8], nprimes=200)
    total += run(32, [5, 6, 7, 8], nprimes=120)
    print(f"\n############ TOTAL (n,s) classes with a REFUTING defect (eta>eta_crit): {total} ############")
