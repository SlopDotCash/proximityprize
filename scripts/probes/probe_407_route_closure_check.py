#!/usr/bin/env python3
"""
probe_407_route_closure_check.py  --  #407: does the lattice-count route actually CLOSE?

Established (probe_407_minkowski_latticecount.py):
  defect at depth r <=> short vectors c in P with |c|_1<=2r. For n=2^mu, reduction mod Phi_n=X^D+1
  (D=n/2) is the isometric fold X^{D+k}=-X^k, so L1 is preserved: defect alpha are EXACTLY nonzero
  c in Z^D with |c|_1<=2r lying in P. Empirically N_def(2r,p) = 0 while Vol_1(2r,D) < p, and
  ~ Vol_1(2r,D)/p after (clean 1/p Gaussian/Minkowski heuristic; ratio measured 0.836).

  => FIRST defect depth r* solves Vol_1(2r*,D) ~ p. With Vol_1(L,D) ~ (2L)^D/D! and prize p=(2D)^beta:
        (4r*)^D/D! ~ (2D)^beta  =>  4r* ~ (D!)^{1/D} (2D)^{beta/D} ~ (D/e)(2D)^{beta/D}
        =>  r* ~ (D/(4e)) (2D)^{beta/D}  ->  D/(4e) = n/(8e)  for large D.

  Moment method needs depth r_opt ~ ln p = beta ln n.

THE CLOSURE TEST (this probe): two independent checks.
  (1) SEPARATION:  is r* >> r_opt in the prize regime?  Tabulate r*(approx, exact Vol_1 inversion)
      vs r_opt = ln p, for n=2^mu, mu=3..20, beta in {4,5}. If r* > r_opt for all large mu, then
      defect=0 throughout the moment-optimization window -- the inflation NEVER bites.
  (2) DELIVERY: with defect=0 up to r_opt, the moment bound runs on the PURE char-0 energy
      E_r^(0). Does min_{r<=r*} (p E_r^(0))^{1/2r} hit C sqrt(n log(p/n))?  We use the exact char-0
      even-moment asymptotic E_r^(0) ~ (2r-1)!! n^r (valid for r << n; sub-Gaussian) and optimize.

If BOTH hold: the route gives, RIGOROUSLY MODULO the Gaussian-heuristic count being an UPPER bound,
B <= C sqrt(n log(p/n)). The remaining open piece is then exactly: PROVE N_def(2r,p) <= Vol_1(2r,D)/p
* (1+o(1)) as an UPPER bound (or even just that it stays o(E_r^(0)/n^r ...)) -- a short-vector
COUNTING upper bound for the ideal lattice P. We pinpoint whether that is a theorem or itself open.

Run:  python scripts/probes/probe_407_route_closure_check.py
"""
import math


def vol_L1(L, D):
    """#{c in Z^D : |c|_1 <= L} = sum_{s=0}^{min(D,L)} C(D,s) C(L,s) 2^s  (exact)."""
    return sum(math.comb(D, s) * math.comb(L, s) * 2 ** s for s in range(0, min(D, L) + 1))


def first_defect_depth(D, p):
    """smallest r with Vol_1(2r,D) >= p (the Minkowski/Gaussian onset of short vectors in P)."""
    r = 1
    while vol_L1(2 * r, D) < p:
        r += 1
        if r > 10 * D:
            return None
    return r


def main():
    print("=" * 92)
    print(" #407 ROUTE CLOSURE CHECK:  r* (first defect depth) vs r_opt (moment depth ~ ln p)")
    print("=" * 92)
    print("\n(1) SEPARATION TEST: prize regime p = n^beta, n=2^mu, D=phi(n)=n/2.")
    print(f"   {'mu':>3} {'n':>8} {'D':>7} {'beta':>5} {'p~2^':>7} {'r_opt=ln p':>11} "
          f"{'r* (Vol~p)':>11} {'r*/r_opt':>9} {'closes?':>8}")
    closes_all = True
    for mu in range(3, 21):
        n = 1 << mu
        D = n // 2
        for beta in (4, 5):
            p = n ** beta  # exact integer
            r_opt = math.log(p)              # ln p (natural log; the optimal moment depth)
            rstar = first_defect_depth(D, p)
            if rstar is None:
                # Vol_1 never reaches p within 10D => r* > 10D, certainly >> r_opt
                rstar_disp = f">{10*D}"
                ratio = float('inf')
                ok = True
            else:
                rstar_disp = str(rstar)
                ratio = rstar / r_opt
                ok = rstar > r_opt
            closes_all = closes_all and ok
            print(f"   {mu:>3} {n:>8} {D:>7} {beta:>5} {math.log2(p):>7.1f} {r_opt:>11.2f} "
                  f"{rstar_disp:>11} {ratio if ratio!=float('inf') else 999:>9.2f} "
                  f"{'YES' if ok else 'NO':>8}")
    print(f"\n   SEPARATION verdict: r* > r_opt for ALL tested (mu,beta)?  {closes_all}")
    print("   (If YES: the p-defect onset depth is strictly beyond the moment-optimization depth,")
    print("    so in the entire window r in [2, r_opt] the energy E_r EQUALS the char-0 value")
    print("    -- the inflation that breaks the naive moment route NEVER occurs in regime.)")

    print("\n(2) DELIVERY TEST: char-0 moment bound min_r (p E_r^(0))^{1/2r}, E_r^(0)=(2r-1)!! n^r,")
    print("    optimized over r <= r* (must stay below onset). Compare to C0 sqrt(n log(p/n)).")
    print(f"   {'mu':>3} {'n':>8} {'beta':>5} {'best r':>7} {'B_moment':>12} {'log2':>7} "
          f"{'target log2':>11} {'gap (log2)':>11}")
    def log_double_fact_odd(r):
        # ln((2r-1)!!) = ln((2r)! / (2^r r!))
        return math.lgamma(2 * r + 1) - r * math.log(2) - math.lgamma(r + 1)
    for mu in range(6, 21):
        n = 1 << mu; D = n // 2
        for beta in (4, 5):
            p = n ** beta
            lnp = math.log(p)
            rstar = first_defect_depth(D, p) or (10 * D)
            best = None
            for r in range(2, min(rstar, 4 * int(lnp) + 5)):
                # log2 of (p E_r^(0))^{1/2r}
                logB = (math.log2(p) + (log_double_fact_odd(r) + r * math.log(n)) / math.log(2)) / (2 * r)
                if best is None or logB < best[1]:
                    best = (r, logB)
            target = 0.5 * math.log2(n * math.log(p / n))   # log2 sqrt(n log(p/n))
            print(f"   {mu:>3} {n:>8} {beta:>5} {best[0]:>7} {2**best[1]:>12.1f} {best[1]:>7.2f} "
                  f"{target:>11.2f} {best[1]-target:>+11.2f}")
    print("\n   DELIVERY verdict: if 'best r' <= r* (onset) AND gap ~ const (B_moment = C sqrt(n log)),")
    print("   then the char-0 moment method, run inside the no-defect window, DELIVERS the target")
    print("   up to the constant C0. The gap column is log2(C0_effective).")


if __name__ == "__main__":
    main()
