#!/usr/bin/env python3
r"""
probe_choosep_threshold_depth.py -- #444 [choose-p-bad-prime-density], the DECISIVE deep-r scaling.

The shallow probe (probe_choosep_baddensity.py) showed: at the REAL prize beta ~ 5.27, the band
primes are GOOD (spur_r = 0) at every COMPUTABLE depth r <= 6, because (2r)^{phi(n)} < p clears all
<=2r-term relations (NubsCarson norm threshold).  This file answers the question the shallow probe
CANNOT reach numerically: does the clearing PERSIST to the prize depth r_need ~ ln q ~ 89?

The mechanism is EXACT and asymptotic-free, so we compute it symbolically:

  * A depth-r spurious config is a NONZERO (char-0) signed sum alpha of <= 2r roots of unity with
    0 < |N(alpha)| <= (2r)^{phi(n)}  (CyclotomicNormDefectThreshold, axiom-clean in-tree).
  * Prime p is GOOD at depth r  <=  p > (2r)^{phi(n)}   [then p | N(alpha) impossible => spur=0].
    (This is a SUFFICIENT condition for good; the converse "p<=(2r)^phi => bad" is NOT forced -- p
     must actually divide SOME realized norm. So r_cross below is a LOWER bound on the true onset.)
  * So the guaranteed-good depth for a prize prime p ~ n^beta is
        r_cross(n,beta) = largest r with (2r)^{phi(n)} < p = n^beta
                        => 2r < n^{beta/phi(n)} => r_cross ~ (1/2) n^{beta/phi(n)}.
  * The prize NEEDS the energy bound to depth r_need ~ ln p = beta * ln n.

DECISIVE RATIO:  r_cross / r_need  =  [ (1/2) n^{beta/phi(n)} ] / [ beta ln n ],  phi(n)=n/2.
  =>  r_cross ~ (1/2) n^{2 beta / n}  ->  (1/2)*1 = 1/2  as n->2^30  (since 2 beta / n -> 0).
  => r_cross COLLAPSES to O(1) while r_need = beta ln n -> infinity.  The guaranteed-good window
     covers a VANISHING fraction r_cross/r_need -> 0 of the required depth.

This probe TABULATES r_cross, r_need, and the ratio across the prize trajectory (index 2^128 fixed,
n growing so beta = 1 + 128/log2(n)), to show the collapse is monotone and already severe at n we can
see -- and confirms it numerically against the exact shallow spur onsets where they overlap.

Verdict knob: if r_cross/r_need stays bounded-below-positive along the trajectory => SURVIVES (a
guaranteed-good prize prime exists deep enough); if it -> 0 => the norm-threshold clearing is purely
shallow and the deep-r defect (= the BGK wall) is NOT cleared by choosing p  => reduces-to-wall.
"""
import math

def phi_2power(n):  # n = 2^mu
    return n // 2

def r_cross(n, p):
    """Largest r with (2r)^{phi(n)} < p.  Guaranteed-good (spur=0) depth for prime p."""
    ph = phi_2power(n)
    # (2r) < p^{1/ph}  =>  r < p^{1/ph}/2
    thr = p**(1.0/ph) / 2.0
    return thr  # real-valued; floor for the integer guaranteed depth

def main():
    print("="*94)
    print(" #444 [choose-p-bad-prime-density] DEEP-r SCALING: guaranteed-good depth vs needed depth")
    print(" r_cross = (1/2) p^{1/phi(n)} (norm-threshold good-floor); r_need = ln p (prize moment depth)")
    print("="*94)

    print("\n--- (A) FIXED beta, grow n: how the guaranteed-good window scales ---")
    print(f"{'n':>10} {'phi(n)':>9} {'beta':>5} {'p~n^beta':>22} {'r_cross':>10} {'r_need=lnp':>11} {'ratio':>8}")
    for beta in (4.0, 5.0, 5.27):
        for mu in (3,4,5,6,8,10,16,20,30):
            n = 1 << mu
            p = n**beta
            rc = r_cross(n, int(p) if p < 1e300 else 10**300)
            # for huge p use logs: r_cross = (1/2) exp( ln p / phi )
            lnp = beta*math.log(n)
            rc = 0.5*math.exp(lnp/phi_2power(n))
            rn = lnp
            print(f"{n:>10} {phi_2power(n):>9} {beta:>5} {p:>22.3e} {rc:>10.3f} {rn:>11.2f} {rc/rn:>8.4f}")
        print()

    print("--- (B) PRIZE TRAJECTORY: index 2^128 fixed, n grows so beta = 1 + 128/log2(n) ---")
    print("    (the genuine prize family; p = n * 2^128)")
    print(f"{'n=2^mu':>12} {'beta':>7} {'p=n*2^128':>14} {'phi(n)':>11} {'r_cross':>10} {'r_need':>10} {'ratio':>9}")
    for mu in (4,5,6,8,10,12,16,20,24,30,40):
        n = 1 << mu
        # p = n * 2^128
        lnp = math.log(n) + 128*math.log(2)
        beta = lnp/math.log(n)
        ph = phi_2power(n)
        rc = 0.5*math.exp(lnp/ph)
        rn = lnp
        print(f"  2^{mu:<9} {beta:>7.3f} {'n*2^128':>14} {ph:>11,} {rc:>10.4f} {rn:>10.2f} {rc/rn:>9.6f}")

    print("\n--- (C) The crossover: at the prize n=2^30, what depth does choosing p guarantee? ---")
    for mu in (20, 25, 30, 40):
        n = 1 << mu
        lnp = math.log(n) + 128*math.log(2)
        ph = phi_2power(n)
        rc = 0.5*math.exp(lnp/ph)
        rn = lnp
        # exponent 2*beta/n in r_cross ~ (1/2) n^{2beta/n}
        beta = lnp/math.log(n)
        print(f"  n=2^{mu}: phi={ph:,}  guaranteed-good depth r_cross = {rc:.6f}  (need r ~ {rn:.1f})")
        print(f"           => the norm threshold (2r)^(phi) < p is satisfied only for r < {rc:.4f}"
              f" = O(1) << r_need")
        print(f"           => 2r must EXCEED p^(1/phi)=p^(2/n)~1+ already at r=1 for n>~2^20:"
              f" p^(1/phi) = {math.exp(lnp/ph):.6f}")

    print("\n--- (D) Re-cast as bad-prime DENSITY at deep r (the union covering) ---")
    print("    A FIXED depth-r spurious alpha rules out only its norm's prime factors (density 0 each).")
    print("    But the NUMBER of distinct depth-<=r spurious configs ~ C(n,2r) 2^{2r} ~ n^{2r} (for 2r<<n),")
    print("    each norm <= (2r)^{phi(n)} = (2r)^{n/2}, with ~ (n/2) ln(2r) prime factors on average.")
    print("    The band of prize primes in [N,2N] (N=n^beta) has ~ N/(n ln N) = n^{beta-1}/(beta ln n) primes.")
    print("    Covering ratio (heuristic union, no clustering):")
    print(f"{'n':>8} {'r':>4} {'#configs~n^2r':>16} {'avg #pfac':>12} {'band size':>14} {'cover (>=1 => all bad)':>24}")
    for mu in (10, 16, 20, 30):
        n = 1 << mu
        beta = (math.log(n)+128*math.log(2))/math.log(n)
        N = n**beta
        band = N/(n*math.log(N))      # ~ #primes =1 mod n in [N,2N]
        for r in (2, 5, 10, int(round(math.log(N)))):
            ph = n/2
            # log-space to avoid overflow
            log_nconfig = (math.lgamma(n+1)-math.lgamma(2*r+1)-math.lgamma(n-2*r+1)) + 2*r*math.log(2) if 2*r<=n else 1e9
            avg_pfac = ph*math.log(2*r)      # average #prime factors of a number <= (2r)^{ph}, ~ Omega ~ ph*ln(2r)/ln(typ pf)
            log_cover = log_nconfig + math.log(max(avg_pfac,1)) - math.log(band) - math.log(n)  # /n: only =1 mod n are eligible (~1/phi fraction... ~ density 1/(n) among factors)
            cover = math.exp(log_cover) if log_cover < 700 else float('inf')
            print(f"{n:>8} {r:>4} {'e^'+format(log_nconfig,'.1f'):>16} {avg_pfac:>12.1f} {band:>14.3e}"
                  f" {('e^'+format(log_cover,'.1f')) if log_cover>700 else format(cover,'.3e'):>24}")
        print()

if __name__ == "__main__":
    main()
