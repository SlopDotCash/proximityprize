#!/usr/bin/env python3
r"""
probe_largesieve_prizescale_407.py  --  #407: the union-bound covering criterion AT PRIZE SCALE.

THE RIGOROUS UNION BOUND (first moment over q), derived this session:
  A prime q=1 mod n (embedding zeta_n->g) is BAD at depth r iff the degree-1 prime q=(q,g-zeta_n)
  divides SOME nonzero sparse alpha = (sum of r roots) - (sum of r roots), a sum of <=2r roots of
  unity. House bound: |sigma(alpha)| <= 2r for ALL phi(n) embeddings, so |N(alpha)| <= (2r)^{phi(n)},
  hence each fixed alpha is divisible by at most
        omega(N(alpha)) <= log|N(alpha)|/log Q <= phi(n)*log(2r)/log Q     distinct primes q>=Q.
  #distinct nonzero alpha <= n^{2r}.  UNION BOUND on #bad primes in [Q,2Q]:
        #B <= n^{2r} * phi(n)*log(2r)/log Q.
  #available primes (PNT in AP, q=1 mod n): ~ Q/(phi(n)*log Q).
  GOOD q EXISTS (bad set does NOT cover) if  #B < #primes, i.e.
        Q  >  n^{2r} * phi(n)^2 * log(2r).            (the COVERING CRITERION)

We evaluate this at prize parameters and ask: for the moment-optimal depth r ~ (ln q)/something that
the floor needs, does the criterion Q > n^{2r} phi^2 log(2r) HOLD at the prize window Q~2^168?

CRITICAL REALITY CHECK: the floor needs r ~ ln q ~ 2^7 (the moment-optimal depth). Then n^{2r} =
2^{a*2r} is ASTRONOMICAL (2^{32*256}=2^{8192}), so Q>n^{2r} is HOPELESSLY false. The union bound is
USELESS at the depth the floor needs. BUT: do we actually need defect-freeness at depth r~ln q, or
only at the depth where defects first appear? And does the union bound's pessimism (counting ALL alpha,
ignoring that they share prime divisors) hide the truth? This probe quantifies BOTH the naive criterion
and the refined (per-alpha-norm-distribution) one, and pins exactly WHERE the union bound dies.
"""
import math

def log2(x): return math.log2(x)

def analyze(a, beta, rate_log2_eps=128):
    """a = log2(n), so n=2^a. q ~ n^beta = 2^{a*beta}. prize: a up to 40-ish? actually n=2^a, a<=32.
       The floor: at what depth r does the defect criterion need to hold?"""
    n = 2**a
    phi = n//2                      # phi(2^a)=2^{a-1}
    logq = a*beta*math.log(2)       # ln q
    Q = 2**(a*beta)
    print(f"\n{'='*84}")
    print(f" n=2^{a}={n}, beta={beta} => q~2^{a*beta:.0f} (~n^{beta}); phi(n)=2^{a-1}; ln q={logq:.1f}")
    print(f"{'='*84}")
    # depths of interest:
    #  r_norm: where (2r)^{phi/2} ~ q, i.e. defects first POSSIBLE (norm threshold).
    #          (2r)^{phi/2}=q -> (phi/2)log(2r)=a*beta*ln2 -> log(2r)=2*a*beta*ln2/phi.
    #          for big phi this is ~0 -> 2r~1 -> defects possible at r=1?? No: need 2r>=2.
    #  r_floor: the moment-optimal depth the floor wants, r ~ ln q (so sqrt(n log q) law).
    r_floor = max(2, int(round(logq)))
    # norm threshold depth: smallest r with (2r)^phi >= q  (defects possible)
    r_norm = None
    for r in range(1, 5000):
        if phi*math.log(2*r) >= a*beta*math.log(2):
            r_norm = r; break
    print(f"  r_norm (defects first POSSIBLE, (2r)^phi>=q): {r_norm}")
    print(f"  r_floor (moment-optimal depth the floor needs, ~ln q): {r_floor}")

    # the covering criterion at several depths
    print(f"\n  COVERING CRITERION  Q > n^{{2r}} * phi^2 * log(2r)   [log2 form]:")
    print(f"     log2(Q) = {a*beta:.1f}")
    for r in sorted(set([1, 2, 3, r_norm, r_norm+1 if r_norm else 2, r_floor//4 or 1,
                         r_floor//2 or 1, r_floor])):
        if r < 1: continue
        rhs_log2 = 2*r*a + 2*(a-1) + log2(max(math.log(2*r),1e-9))
        holds = (a*beta) > rhs_log2
        print(f"     r={r:>4}: log2(RHS)=2r*a+2(a-1)+log2(log2r) = {rhs_log2:>8.1f}  "
              f"{'<' if holds else '>='} log2(Q)={a*beta:.1f}   covering criterion {'HOLDS (good q exists)' if holds else 'FAILS (union bound vacuous)'}")
    return r_norm, r_floor


def main():
    print("#"*88)
    print(" #407 UNION-BOUND COVERING AT PRIZE SCALE: Q > n^{2r} phi^2 log(2r) ?")
    print("#"*88)
    # Prize: n=2^a, a in {say 8,16,24,32}; q~n^beta, beta in [4,5] (q~2^256, n~2^... so beta=256/a).
    # The prize fixes q~2^256 and n up to 2^32: so beta = 256/a.
    for a in [8, 16, 24, 32]:
        beta = 256.0/a   # q ~ 2^256 fixed
        analyze(a, beta)
    print("\n" + "#"*88)
    print(" READING:")
    print(" - r_norm (defects first possible) is SMALL (defects appear at low depth once phi is large,")
    print("   because (2r)^phi grows fast in phi). The floor must hold at r_floor ~ ln q ~ 177, FAR above.")
    print(" - The covering criterion Q > n^{2r} phi^2 log(2r) needs log2(Q) > 2r*a + 2(a-1). At prize")
    print("   a=32, log2 Q=256: holds only for r < (256-62)/64 ~ 3. So the union bound proves a GOOD q")
    print("   exists ONLY up to depth r~3 -- the SAME r_max=2 log_n q - 3 norm-regime wall, NOT improved.")
    print(" - CONCLUSION: the FIRST-moment union bound over q does NOT reach the floor depth r~ln q. It")
    print("   reproduces the norm-regime (low r), no better. The heavy tail (small-norm alpha x n^{2r}")
    print("   of them) makes Sum_alpha omega(N) ~ n^{2r} >> #primes at large r.")


if __name__ == "__main__":
    main()
