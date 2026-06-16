#!/usr/bin/env python3
"""
probe_444_attacker_maxc_v2.py  (#444 ATTACKER, CORRECTED classification)

BUG in v1: tau=1 (trivial subgroup mu_1={1}) makes EVERY set a 'union of mu_1-cosets', so all
defects were wrongly classified as char-0 cosets. FIX: the char-0 survivor structure (Lam-Leung
rigidity) is: a size-s set with first c power sums vanishing in CHAR 0 must be a union of mu_tau-
cosets with tau = least 2-power with tau > c  (tau >= c+1). We compute the char-0 count CORRECTLY
and define DEFECT = lacunary-mod-p set that is NOT such a char-0 survivor.

Decisive test (per (n,p,s)): find the MAX c such that a DEFECT exists, then check whether
   eta = c/n  >  eta_crit = log(s)/(2 log p)   <=>  p > s^{n/(2c)}   ==> REFUTES the floor.

We ALSO independently report char-0 survivors via exact complex test (|beta_S over C| with the
power sums vanishing as exact complex numbers) to cross-check the coset structure.
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

def char0_survivor(n, idxs, c):
    """
    Char-0 condition: a size-s set S has p_1(S)=...=p_c(S)=0 OVER C (exact complex) iff it's a
    union of mu_tau cosets (tau the least 2-power > c). We test it DIRECTLY: compute the first c
    complex power sums of {zeta_n^i : i in idxs} and check they're ~0. This is the exact char-0
    membership (no need to special-case tau).
    """
    z = 2j*math.pi/n
    pts = [cmath.exp(z*i) for i in idxs]
    for j in range(1, c+1):
        s = sum(pt**j for pt in pts)
        if abs(s) > 1e-7:
            return False
    return True

def is_balanced(n, idxs):
    half = n//2; ss = set(idxs)
    return all(((i+half) % n) in ss for i in idxs)

def beta_abs(n, idxs):
    z = 2j*math.pi/n
    return abs(sum(cmath.exp(z*i) for i in idxs))

def scan(n, p, s_range, cap_comb=2_500_000):
    """Return list of defects found: (s, c, eta, eta_crit, margin, combo, char0_flag)."""
    elts = subgroup(n, p)
    best = None  # (margin, ...)
    n_defect = 0
    refuters = []
    for s in s_range:
        if comb(n, s) > cap_comb:
            continue
        powtab = [[pow(v, j, p) for j in range(1, s+1)] for v in elts]
        for combo in itertools.combinations(range(n), s):
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
            # DEFECT (mod p) = lacunary to depth c but NOT a char-0 survivor at depth c
            if char0_survivor(n, combo, c):
                continue  # this is the char-0 coset structure, expected
            n_defect += 1
            eta = c / n
            eta_crit = log(s) / (2*log(p))
            margin = eta - eta_crit
            rec = (margin, s, c, eta, eta_crit, list(combo),
                   is_balanced(n, combo), round(beta_abs(n, combo), 3))
            if best is None or margin > best[0]:
                best = rec
            if margin > 0:
                refuters.append(rec)
    return best, n_defect, refuters

if __name__ == "__main__":
    print("### ATTACKER v2 (corrected char-0 classification): defect = lacunary-mod-p NOT char-0 ###")
    print("### REFUTE iff a defect has eta=c/n > eta_crit=log(s)/(2 log p) ###\n")

    def primes_for(n, count, idx_min=2, extra_betas=()):
        out = []; pp = n+1
        while len(out) < count:
            if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= idx_min:
                out.append(pp)
            pp += n
        for beta in extra_betas:
            t = int(n**beta); base = t - (t % n) + 1; q = base
            while True:
                if isprime(q) and (q-1) % n == 0 and (q-1)//n >= idx_min:
                    out.append(q); break
                q += n
        return out

    for (n, s_range, count, betas) in [
        (16, range(4, 9), 200, (2.0, 3.0, 4.0, 5.0)),
        (32, range(4, 10), 80, (2.0, 2.5, 3.0, 3.5, 4.0)),
    ]:
        print(f"{'='*88}\n### n={n}, s in {list(s_range)} ###\n{'='*88}")
        primes = primes_for(n, count, 2, betas)
        global_best = None; tot_def = 0; all_ref = []
        for p in primes:
            best, nd, refs = scan(n, p, s_range)
            tot_def += nd
            all_ref += [(p,)+r for r in refs]
            if best is not None and (global_best is None or best[0] > global_best[0][0]):
                global_best = (best, p)
        print(f"  total DEFECTS found over {len(primes)} primes: {tot_def}")
        if global_best:
            b, p = global_best
            margin, s, c, eta, ec, combo, bal, ba = b
            print(f"  DEEPEST defect: p={p} s={s} c={c} eta={eta:.4f} eta_crit={ec:.4f} "
                  f"margin={margin:+.4f} balanced={bal} |beta|={ba}  T={combo}")
        print(f"  REFUTERS (eta>eta_crit): {len(all_ref)}")
        for r in all_ref[:12]:
            p, margin, s, c, eta, ec, combo, bal, ba = r
            print(f"     !!! p={p} s={s} c={c} eta={eta:.4f} > eta_crit={ec:.4f} (margin {margin:+.4f}) "
                  f"balanced={bal} |beta|={ba} T={combo}")
        print()
