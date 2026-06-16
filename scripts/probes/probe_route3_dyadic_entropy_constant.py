#!/usr/bin/env python3
"""Route 3 (#444): pin the closed constant c(rho) from the dyadic symmetric-tower base count.

GOVERNING LAW (in-tree, proven): delta* = (1-rho) - c(rho)/log2(n), where c(rho) is the
exponential constant in the worst-window list L*(eta) = 2^{c(rho)/eta}, set by crossing the
budget eps*|F| ~ n.

The binding bad-scalar mass (KKH26WitnessSpread.lean, proven in-tree) at radius
delta = 1 - r/s on the dyadic part s = 2^mu = n/m is exactly

    M(s, r) = 2^r * C(s/2, r).

The code degree is d = (r-2)*m so the rate is rho = d/n = (r-2)/s ~ r/s, i.e. r ~ rho*s, and
the radius is delta = 1 - r/s ~ 1 - rho = capacity. The "cushion" eta = (1-rho) - delta
= (r/s - rho) = 2/s at the EXACT KKH26 family; the entropy phrasing instead sweeps r and reads
the exponent of M per dyadic coordinate.

This probe extracts the EXACT exponent constant
    c_exact(rho) := lim_{s->inf} (1/s) * log2( M(s, r=round(rho*s)) )
and compares it to three candidate closed forms in rho:
    (A) H_2(rho)                       [binary entropy, KKH26 Appendix-A claim]
    (B) H_2(rho) + rho                 [the 2^r factor on top of the binomial]
    (C) (1/2) H_2(2 rho)               [if the binomial is C(s/2, r) read at argument 2r/s]
and the SYMMETRIC-TOWER variant where r counts sign-free subsets of the half-group s/2:
    M_sym(s, r) = C(s/2, r)  (the L_sym base count, no 2^r), constant (1/2)H_2(2 rho).
"""
from math import log2, comb


def log2binom(n, k):
    """EXACT log2 C(n,k) via Python big-int comb (lgamma loses precision at s~2^30)."""
    if k < 0 or k > n:
        return float("-inf")
    if k == 0 or k == n:
        return 0.0
    M = comb(n, k)
    b = M.bit_length() - 1
    return b + log2(M / 2 ** b)


def H(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * log2(p) - (1 - p) * log2(1 - p)


def main():
    print("Route 3: exponent constant of the dyadic bad-scalar mass per coordinate, c = (1/s) log2 M")
    print()
    print("KKH26 count  M(s,r) = 2^r * C(s/2, r),  r = round(rho*s)  (the BINDING mass)")
    print(f"{'rho':>7} {'s':>9} {'r':>7} {'c_exact':>10} {'H2(rho)':>9} "
          f"{'H2+rho':>9} {'(1/2)H2(2rho)':>14}")
    rows = {}
    for rho in (0.5, 0.25, 0.125, 0.0625):
        last = None
        for a in (6, 8, 10, 12, 16, 20, 24, 30):
            s = 2 ** a
            r = round(rho * s)
            if r < 1 or r > s // 2:
                continue
            logM = r + log2binom(s // 2, r)          # log2( 2^r C(s/2,r) )
            c_exact = logM / s
            last = c_exact
            candA = H(rho)
            candB = H(rho) + rho
            candC = 0.5 * H(2 * rho)
            mark = "  <-" if a == 30 else ""
            print(f"{rho:>7} {s:>9} {r:>7} {c_exact:>10.5f} {candA:>9.5f} "
                  f"{candB:>9.5f} {candC:>14.5f}{mark}")
        rows[rho] = last
        print()

    print("SYMMETRIC-TOWER base count  M_sym(s,r) = C(s/2, r)  (L_sym recursion, NO 2^r factor)")
    print(f"{'rho':>7} {'s':>9} {'r':>7} {'c_sym_exact':>12} {'(1/2)H2(2rho)':>14} {'H2(rho)':>9}")
    for rho in (0.5, 0.25, 0.125, 0.0625):
        for a in (16, 24, 30):
            s = 2 ** a
            r = round(rho * s)
            if r < 1 or r > s // 2:
                continue
            logMs = log2binom(s // 2, r)
            c_sym = logMs / s
            print(f"{rho:>7} {s:>9} {r:>7} {c_sym:>12.5f} {0.5*H(2*rho):>14.5f} {H(rho):>9.5f}")
        print()

    print("VERDICT scan (per-coordinate exponent of the binding KKH26 mass, s=2^a):")
    for rho in (0.5, 0.25, 0.125, 0.0625):
        ce = rows[rho]
        cand = rho + 0.5 * H(2 * rho)
        print(f"  rho={rho:>6}: c_exact={ce:.5f}  =  rho+(1/2)H2(2rho)={cand:.5f}  "
              f"(err={abs(cand-ce):.2e})   [H2(rho)={H(rho):.5f}]")

    print()
    print("=" * 78)
    print("CROSSOVER (the governing law): delta* = (1-rho) - c(rho)/log2(n).")
    print("Finest cushion eta=1/s on the integer granularity ladder; smallest length s* with")
    print("the bad mass 2^r*C(s/2,r) (r=floor(rho*s)+1) exceeding budget mu=log2(q eps*)~log2 n.")
    print("Then c(rho) = eta*·mu = mu/s*.  Closed prediction: c(rho) = rho + (1/2)H2(2rho).")
    print(f"{'rho':>7} {'mu':>7} {'s*':>8} {'c=eta*·mu':>10} {'rho+1/2H2(2rho)':>16} {'H2(rho)':>9}")
    for rho in (0.25, 0.125, 0.0625):
        G = rho + 0.5 * H(2 * rho)
        for mu in (4000, 16000, 64000):
            sstar = None
            for s in range(4, int(8 * mu / G) + 100, 2):
                r = int(rho * s) + 1
                if r > s // 2:
                    continue
                if r + log2binom(s // 2, r) > mu:
                    sstar = s
                    break
            c = mu / sstar
            print(f"{rho:>7} {mu:>7} {sstar:>8} {c:>10.5f} {G:>16.5f} {H(rho):>9.5f}")
        print()
    print("CONCLUSION: Route 3 yields the CLOSED constant  c(rho) = rho + (1/2)*H2(2*rho),")
    print("NOT H2(rho).  The (1/2)H2(2rho) part is the C(s/2,r) symmetric-tower base binomial")
    print("(Stirling); the +rho part is the 2^r singleton/sign correction.")
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
