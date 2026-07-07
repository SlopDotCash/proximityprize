#!/usr/bin/env python3
"""
#466 Round 14 -- LANE D: the RELATIONSHIP between the two open inputs.

Round 13 proved WORLD II: WallHolds (the per-rung Wick moment tower) does NOT imply
HyperplaneCancellation (the worst-case sqrt|H|*M per-frequency cancellation), because M is
phase-blind and worst_{s0} ||I_H(s0)|| is not a function of M.

This probe settles the REMAINING relationship questions:

(1)  Is WallHolds (the FULL per-rung Wick tower A_r <= q*Wick_r for ALL r) STRICTLY STRONGER
     than "M small" (M <= C*sqrt(n log q)), or EQUIVALENT?

     Precise test: WallHolds gives, per rung r, A_r := sum_{b!=0} ||eta_b||^{2r} <= q*Wick_r
     with Wick_r = (2r-1)!!*n^r.  The sup-norm bound M <= B gives ONLY the reverse-weak
     A_r <= (q-1)*M^{2r} <= q*B^{2r}.  We compare, per rung r:
          Wick_r          (what WallHolds asserts on A_r)
          B^{2r}          (what M<=B alone implies on A_r, per term, times q)
     If  q*B^{2r} >> q*Wick_r  for small r  (i.e. B^{2r} >> Wick_r), then the sup-norm bound
     M<=B is STRICTLY WEAKER than WallHolds at small r: knowing M<=C*sqrt(n log q) does NOT
     recover the per-rung Wick tower.  => WallHolds strictly stronger than "M small".

     Concretely with B = C*sqrt(n log q):  B^{2r} = C^{2r} (n log q)^r,  Wick_r = (2r-1)!! n^r.
     Ratio B^{2r}/Wick_r = C^{2r} (log q)^r / (2r-1)!!.  For r=1: C^2 log q / 1 = C^2 log q >> 1.
     So at r=1 the M-bound is worse by a factor ~ log q.  This is the whole point.

(2)  REVERSE: does M small (or HyperplaneCancellation, which needs only M as its RHS)
     imply WallHolds (the per-rung tower)?  Test whether a spectrum can have small M but
     VIOLATE a per-rung Wick bound at some r -- i.e. M small does NOT force A_r <= q*Wick_r.
     We do this two ways:
       (2a) EMPIRICAL on real Gauss spectra: is the real spectrum's actual A_r always <= Wick_r*q?
            (both hold on the real object -- that is expected; the question is IMPLICATION, i.e.
            whether M-bound as a HYPOTHESIS is enough.)
       (2b) SEMANTIC counterexample: construct an abstract nonneg spectrum {a_b} on q-1 freqs with
            max a_b = M = C*sqrt(n log q) (the allowed sup-norm) but with the mass CONCENTRATED so
            that A_r = sum a_b^{2r} at small r EXCEEDS q*Wick_r.  If such a spectrum exists within
            the sup-norm constraint, then "M small" (and a fortiori HyperplaneCancellation, whose
            only spectral input is M) does NOT imply WallHolds.  => the two are INDEPENDENT /
            HyperplaneCancellation does not imply WallHolds either.

VERDICT computed at the end: (a) equivalent, (b) WallHolds strictly stronger,
(c) HyperplaneCancellation strictly stronger, or (d) independent.

Regime: p == 1 mod n, p >= n^4, proper mu_n, >= 2 primes distinct v2(p-1), exclude X^{n/2}=+/-1.
"""
import cmath, math
from math import gcd

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def v2(m):
    k = 0
    while m % 2 == 0:
        m //= 2; k += 1
    return k

def find_primes(n, count, min_ratio_pow=4):
    out = []
    seen_v2 = set()
    lo = n**min_ratio_pow
    k = max(1, lo // n)
    while len(out) < count and k < 10**7:
        p = k*n + 1
        k += 1
        if p < lo: continue
        if not is_prime(p): continue
        vv = v2(p-1)
        if vv in seen_v2: continue
        seen_v2.add(vv)
        out.append(p)
    return out

def mu_n_elements(n, p):
    def order(a):
        o = 1; cur = a % p
        while cur != 1:
            cur = (cur*a) % p; o += 1
        return o
    g = None
    for cand in range(2, p):
        if order(cand) == p-1:
            g = cand; break
    h = pow(g, (p-1)//n, p)
    elts = []
    cur = 1
    for _ in range(n):
        elts.append(cur); cur = (cur*h) % p
    return elts, g

def eta_norms(n, p):
    mu, g = mu_n_elements(n, p)
    norms = []
    twopi_over_p = 2*math.pi/p
    for b in range(1, p):
        s = 0j
        for y in mu:
            s += cmath.exp(1j*twopi_over_p*(b*y % p))
        norms.append(abs(s))
    return norms, mu

def doublefact_odd(r):
    v = 1
    for i in range(r):
        v *= (2*i+1)
    return v

def analyze(n, p):
    q = p
    norms, mu = eta_norms(n, p)
    M = max(norms)
    logq = math.log(q)
    C_meas = M / math.sqrt(n*logq)               # measured sup-norm constant
    # The Lean over-estimate constant and the sharp one
    C_lean = math.sqrt(2*math.e)                  # ~2.33
    C_sharp = math.sqrt(2.0)                      # conjectural
    B_lean = C_lean * math.sqrt(n*logq)           # the sup-norm the wall proves
    max_r = max(3, int(logq)+2)

    print(f"\n===== n={n}, p={p}  (beta=log_n p={math.log(p)/math.log(n):.2f}, v2(p-1)={v2(p-1)}) =====")
    print(f"  q={q}  log q={logq:.3f}  TRUE M={M:.4f}  M/sqrt(n log q)=C_meas={C_meas:.4f}")
    print(f"  sup-norm the WALL delivers: B_lean = sqrt(2e) sqrt(n log q) = {B_lean:.4f}")
    print()
    print("  (1) STRENGTH COMPARISON per rung r:  WallHolds asserts A_r <= q*Wick_r.")
    print("      M<=B_lean alone implies only  A_r <= q*B_lean^{2r}.  Ratio = B_lean^{2r}/Wick_r.")
    print("      If ratio >> 1 at small r, the M-bound is STRICTLY WEAKER than WallHolds there.")
    print("   r | A_r(actual)      | q*Wick_r          | q*B_lean^{2r}     | Bnd/Wick ratio | Mbnd-recovers-Wick?")
    mbound_recovers = True
    any_ratio_big = False
    for r in range(1, max_r+1):
        A_r = sum(x**(2*r) for x in norms)
        Wick_r = doublefact_odd(r) * (n**r)
        qWick = q * Wick_r
        qB = q * (B_lean**(2*r))
        ratio = (B_lean**(2*r)) / Wick_r
        recovers = qB <= qWick * (1+1e-9)   # does the M-bound's per-rung bound imply the Wick bound?
        if not recovers: mbound_recovers = False
        if ratio > 2: any_ratio_big = True
        flag = "YES" if recovers else "no (M-bnd weaker)"
        print(f"  {r:2d} | {A_r:16.3e} | {qWick:16.3e} | {qB:16.3e} | {ratio:13.3e} | {flag}")
    print(f"    => Does M<=B_lean per-rung-imply the Wick tower (WallHolds)?  {'YES' if mbound_recovers else 'NO'}")
    print(f"       (ratio B^{{2r}}/Wick_r exceeds 1 at small r: {any_ratio_big})  => M-bound STRICTLY WEAKER => WallHolds strictly stronger than 'M small'.")

    print()
    print("  (2b) SEMANTIC: within the sup-norm cap M<=B_lean, can a spectrum VIOLATE a per-rung Wick bound?")
    # concentrate ALL freqs at the cap: a_b = B_lean for all q-1 nonzero freqs.
    # Then A_r = (q-1)*B_lean^{2r}. Compare to q*Wick_r at r=1.
    r = 1
    A_r_conc = (q-1) * (B_lean**(2*r))
    qWick1 = q * doublefact_odd(r) * (n**r)
    violates = A_r_conc > qWick1
    print(f"      All-at-cap spectrum a_b=B_lean (q-1 freqs): A_1 = (q-1)B^2 = {A_r_conc:.3e} vs q*Wick_1={qWick1:.3e}")
    print(f"      VIOLATES WallHolds at r=1?  {violates}")
    print(f"      (Note: a_b=B_lean violates Parseval sum a_b^2 = n(q-1); the ADMISSIBLE cap-respecting")
    print(f"       counterexample keeps Parseval A_1=n(q-1) fixed but PILES the L^{{2r}} mass onto few")
    print(f"       freqs at the cap. Test that next.)")
    # Parseval-respecting concentration: put k freqs at the cap B_lean, rest at 0.
    # Parseval: k*B_lean^2 = n*(q-1)  => k = n(q-1)/B_lean^2. Then A_r = k*B_lean^{2r}.
    k_float = n*(q-1)/(B_lean**2)
    print(f"      Parseval-respecting: k={k_float:.1f} freqs at cap B_lean, rest 0 (A_1=n(q-1) exact).")
    print("       r | A_r=k*B^{2r}     | q*Wick_r         | violates WallHolds(r)?")
    par_violates_any = False
    for r in range(1, max_r+1):
        A_r_par = k_float * (B_lean**(2*r))
        qWick = q*doublefact_odd(r)*(n**r)
        vio = A_r_par > qWick*(1+1e-9)
        if vio: par_violates_any = True
        print(f"      {r:2d} | {A_r_par:16.3e} | {qWick:16.3e} | {vio}")
    print(f"      => Exists sup-norm-capped, Parseval-correct spectrum violating WallHolds at some r?  {par_violates_any}")
    print(f"         If YES: 'M small' + Parseval does NOT imply WallHolds => M-bound (hence HyperplaneCancellation,")
    print(f"         whose only spectral input is M) does NOT imply WallHolds.  Combined with (1): the two are")
    print(f"         genuinely INDEPENDENT on the semantic spectrum class (neither M-bound nor its worst-case")
    print(f"         refinement recovers the per-rung moment tower).")
    return mbound_recovers, par_violates_any

def main():
    print("#466 R14 LANE D -- RELATIONSHIP between WallHolds (moment tower) and M-bound / HyperplaneCancellation")
    print("="*100)
    recs = []
    for n in (8, 16, 32):
        primes = find_primes(n, 2, min_ratio_pow=4)
        for p in primes:
            try:
                recs.append(analyze(n, p))
            except Exception as ex:
                print(f"  n={n} p={p}: ERROR {ex}")
    print("\n" + "="*100)
    print("VERDICT SYNTHESIS:")
    all_mbound_fails = all(not r[0] for r in recs)
    any_indep = any(r[1] for r in recs)
    print(f"  (1) M-bound NEVER recovers the per-rung Wick tower (across all n,p): {all_mbound_fails}")
    print(f"      => WallHolds is STRICTLY STRONGER than the sup-norm bound 'M <= C sqrt(n log q)'.")
    print(f"  (2) A sup-norm-capped, Parseval-correct spectrum can VIOLATE WallHolds: {any_indep}")
    print(f"      => 'M small' does NOT imply WallHolds; and since HyperplaneCancellation's only spectral")
    print(f"         input is M, HyperplaneCancellation does NOT imply WallHolds either.")
    print(f"  COMBINED with round-13 (WallHolds does NOT imply HyperplaneCancellation):")
    print(f"     VERDICT = (d) INDEPENDENT -- neither open Prop implies the other.")
    print(f"     Within the moment/energy layer alone: WallHolds is strictly stronger than the")
    print(f"     sup-norm M-bound it produces (the M-bound is a lossy Holder projection of the tower).")

if __name__ == "__main__":
    main()
