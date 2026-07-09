#!/usr/bin/env python3
"""
sweep_A02_autocorr.py  —  Actionable A02 numerical validation.

Validates, in prize-shaped small cases n=8,16,32, the char-p autocorrelation recursion
and the "free deep tail" of deep-moment-validity (DM_r).

OBJECTS
  H = mu_n  (the n-th roots of unity), realized inside Z/p for a prime p = 1 (mod n).
  f_r(z) = #{(x_1..x_r) in H^r : sum x_i = z}      (r-fold sumset count = 1_H^{*r})
  C_r(z) = sum_w f_r(w) f_r(w-z)                    (autocorrelation of f_r)
  E_r    = sum_z f_r(z)^2 = C_r(0)                  (2r-fold additive energy of H)

CLAIMS CHECKED
  (1) EXACT RECURSION   E_{r+1} = n * E_r + cross_r,  cross_r = sum_{u != v in H} C_r(v-u).
  (2) AUTOCORR CAP      C_r(z) <= C_r(0) = E_r   for all z   (=> cross_r <= n(n-1) E_r).
  (3) CRUDE BOUND       E_r <= n^{2r-1}   (from E_{r+1} <= n^2 E_r, E_1 = n).
  (4) FREE DEEP TAIL    The crude bound (3) ALREADY implies the DM_r target
                        E_r <= (2r-1)!! * n^{r-1}  for all r >= ceil(e n / 2) ~ 1.36 n,
                        UNCONDITIONALLY (no char-0/Lam-Leung input). Crossover r/n -> e/2.
  (5) RESIDUAL BAND     For r in [~log n, 1.36 n) the crude bound EXCEEDS the DM_r target,
                        so the real (char-0 + char-p transfer) input is needed there.
                        ALSO: the moment-method optimum r ~ log q sits BELOW the residual band,
                        so the free deep tail is prize-USELESS (honest).
"""
import math
from math import factorial, comb
from itertools import product

def double_fact_odd(r):       # (2r-1)!! = (2r)! / (2^r r!)
    return factorial(2*r) // (2**r * factorial(r))

def find_prime_1_mod_n(n, lo):
    p = lo
    while True:
        if (p - 1) % n == 0:
            # primality
            ok = p > 1
            for d in range(2, int(p**0.5)+1):
                if p % d == 0:
                    ok = False; break
            if ok:
                return p
        p += 1

def mu_n_elements(n, p):
    """The n distinct n-th roots of unity in Z/p (p = 1 mod n)."""
    # find a primitive root g of Z/p^*
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = (x*a) % p; o += 1
        return o
    g = None
    for cand in range(2, p):
        if order(cand) == p-1:
            g = cand; break
    assert g is not None
    h = pow(g, (p-1)//n, p)   # primitive n-th root
    return [pow(h, j, p) for j in range(n)]

def conv_counts(prev, H, p):
    """prev: dict z->count for f_r ; returns f_{r+1} = prev * 1_H."""
    out = {}
    for z, c in prev.items():
        for u in H:
            w = (z + u) % p
            out[w] = out.get(w, 0) + c
    return out

def energy_from_counts(counts):
    return sum(c*c for c in counts.values())

def autocorr(counts, z, p):
    """C_r(z) = sum_w f_r(w) f_r(w-z)."""
    s = 0
    for w, c in counts.items():
        c2 = counts.get((w - z) % p, 0)
        s += c * c2
    return s

def run(n, rmax_check=4):
    # use a moderately large prime so f_r counts are char-0 (no mod-p wraparound collisions)
    # need p > r*max(H) ~ but coords are residues; to stay char-0 in the SUM we need p > n^something.
    # For the EXACT-RECURSION identity (claim 1,2) any prime works (it's an identity mod p).
    # For comparing E_r to its char-0 value we want p large; use p ~ n^4.
    p = find_prime_1_mod_n(n, n*n*n*n)
    H = mu_n_elements(n, p)
    assert len(set(H)) == n, "roots not distinct"
    # build f_1 = 1_H
    f = {u: 1 for u in H}
    E = {}
    E[1] = energy_from_counts(f)   # = n
    print(f"=== n={n}, p={p} (p~n^4), |H|={len(H)} ===")
    print(f"  E_1 = {E[1]}  (expect n={n}): {'OK' if E[1]==n else 'FAIL'}")
    rows = []
    fr = {1: dict(f)}
    for r in range(1, rmax_check+1):
        cur = fr[r]
        Er = energy_from_counts(cur)
        E[r] = Er
        # claim 2: autocorr cap C_r(z) <= C_r(0)=E_r for all shifts that occur (v-u, u,v in H)
        C0 = Er
        cross = 0
        capok = True
        for u in H:
            for v in H:
                if u == v:
                    continue
                z = (v - u) % p
                Cz = autocorr(cur, z, p)
                if Cz > C0 + 1e-9:
                    capok = False
                cross += Cz
        # claim 1: E_{r+1} = n*E_r + cross
        nxt = conv_counts(cur, H, p)
        fr[r+1] = nxt
        Er1 = energy_from_counts(nxt)
        recok = (Er1 == n*Er + cross)
        # claim 3: crude bound E_r <= n^{2r-1}
        crude = n**(2*r-1)
        crudeok = (Er <= crude)
        # DM_r target (char-0 clean / Gaussian value)  E_r <= (2r-1)!! n^r
        dm = double_fact_odd(r) * n**r
        dmok = (Er <= dm)
        rows.append((r, Er, cross, Er1, n*Er+cross, recok, capok, crude, crudeok, dm, dmok))
        print(f"  r={r}: E_r={Er:<14} cross_r={cross:<16} "
              f"E_{{r+1}}={Er1:<16} n*E_r+cross={n*Er+cross:<16} "
              f"recursion:{'OK' if recok else 'FAIL'}  autocorr-cap:{'OK' if capok else 'FAIL'}")
        print(f"        crude n^(2r-1)={crude:<18} E_r<=crude:{'OK' if crudeok else 'FAIL'}   "
              f"DM target (2r-1)!!*n^r={dm:<18} E_r<=DM(clean):{'OK' if dmok else 'FAIL'}")
    return E

def free_tail_threshold(n):
    """smallest r* s.t. crude bound n^(2r-1) implies DM_r (E_r<=(2r-1)!!*n^r) for ALL r>=r*.
    crude => DM  <=>  n^(2r-1) <= (2r-1)!!*n^r  <=>  n^(r-1) <= (2r-1)!!.
    Note n^(r-1)<=(2r-1)!! holds vacuously at r=1 then fails for a while, so we return the
    threshold beyond which it holds permanently (largest failing r, plus one)."""
    last_fail = 0
    for r in range(1, int(2.2*n) + 6):
        if not (double_fact_odd(r) >= n**(r-1)):
            last_fail = r
    return last_fail + 1

if __name__ == "__main__":
    print("#"*78)
    print("# A02: char-p autocorrelation recursion + free deep tail of DM_r")
    print("#"*78)
    # n=8,16 to r=4; n=32 to r=3 (the r=4 enumeration at n=32 is heavy in pure Python and
    # adds no new info — the exact recursion is an identity, validated already at n=8,16).
    run(8, rmax_check=4); print()
    run(16, rmax_check=4); print()
    run(32, rmax_check=3); print()
    print("-"*78)
    print("FREE-DEEP-TAIL threshold r*: crude bound n^(2r-1) implies DM target (E_r<=(2r-1)!!*n^r)")
    print("for ALL r>=r*  (i.e. n^(r-1) <= (2r-1)!!).  Asymptotic threshold e*n/2 = 1.359 n;")
    print("the clean sufficient bound ceil(e n/2) dominates r* at every n.")
    for n in [8,16,32,64,128,256]:
        r0 = free_tail_threshold(n)
        ce = math.ceil(math.e*n/2)
        print(f"  n={n:<6} r*={r0:<6} r*/n={r0/n:.4f}   e*n/2={math.e*n/2:7.2f}   ceil(e n/2)={ce:<6} "
              f"r*<=ceil: {'OK' if r0<=ce else 'FAIL'}")
    print()
    print("-"*78)
    print("HONEST PRIZE-RELEVANCE CHECK: moment optimum r_opt ~ log q vs free-tail floor 1.36 n.")
    print("Prize: q = p ~ n*2^128, n=2^a.  log q (base e):")
    for a in [25, 32, 40]:
        n = 2**a
        q = n * 2**128
        logq = math.log(q)            # natural log
        ropt = logq                   # moment optimum r ~ ln q
        floor = math.ceil(math.e*n/2)
        print(f"  a={a}: n=2^{a}, ln q={logq:.1f}  =>  r_opt~{ropt:.0f}   free-tail floor 1.36n~{floor:.3e}")
    print("  => r_opt (~hundreds) << free-tail floor (~1.36*2^a).  The free deep tail is")
    print("     UNCONDITIONAL but lives FAR ABOVE the prize-useful moment depth. Honest: it does")
    print("     NOT close the prize; the prize-relevant band [~log n, 1.36n) keeps the real input.")
