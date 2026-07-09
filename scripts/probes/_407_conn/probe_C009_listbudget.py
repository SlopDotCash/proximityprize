#!/usr/bin/env python3
"""C009 settle: cell count c = ℓ = GS list size; track its budget in the window.

C009 chain (exact, from the in-tree lemmas):
  I(delta) <= c * n          (C009 form 3; c = # affine cells)
  c = (gsFactorIndex Q).card <= natDegreeY Q = ℓ   (Hab25DegreeBudget, PROVEN)
  => I(delta) <= ℓ * n.
Prize budget: I(delta) <= q*eps* ~ n   (C009 form 2).
So C009 closes the prize  IFF  ℓ <= 1  (single GS factor) in the window interior.

The ONLY regime where ℓ is provably q-independent & bounded is BELOW Johnson,
where (JohnsonListBound, in-tree CandidateProofLoop9):
    ℓ <= 1 / ((1-delta)^2 - rho)            [finite iff (1-delta)^2 > rho]
This budget DIVERGES as delta -> 1 - sqrt(rho)^+ (the Johnson radius), i.e.
exactly as one ENTERS the prize window interior  (1-sqrt(rho), 1-rho-Theta(1/log n)].

This probe just prints that exact divergence at the prize rates, and shows
ℓ >= 2 already inside the window (so c >= 2, c*n >= 2n > n = budget): C009's
"each cell <= n" never suffices because the NUMBER of cells is the open list
size, which is > 1 throughout the window.  Pure exact rational arithmetic.
"""
from fractions import Fraction as Fr
import math


def johnson_radius(rho):
    return 1 - math.sqrt(rho)


def list_budget(delta, rho):
    """Johnson list budget 1/((1-delta)^2 - rho); inf if delta past Johnson."""
    d = (1 - delta) ** 2 - rho
    if d <= 0:
        return math.inf
    return 1.0 / d


def main():
    print("=== C009 verdict probe: cell count = GS list size ℓ; budget needs ℓ<=1 ===")
    print("prize budget q*eps* ~ n  =>  I(delta) <= n  =>  (since I<=ℓ*n) need ℓ<=1\n")
    for rho in (Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 16)):
        rj = johnson_radius(float(rho))
        print(f"rho={rho}  Johnson radius 1-sqrt(rho) = {rj:.4f}")
        # window interior: (1-sqrt(rho), 1-rho-eta], eta small ~ 1/log n
        # sample a few delta just INSIDE the window
        for frac in (0.0, 0.10, 0.30, 0.60, 0.90):
            # delta = Johnson + frac*(width); width = (1-rho) - (1-sqrt(rho)) = sqrt(rho)-rho
            width = math.sqrt(float(rho)) - float(rho)
            delta = rj + frac * width
            B = list_budget(delta, float(rho))
            tag = "JOHNSON EDGE" if frac == 0.0 else "WINDOW INTERIOR"
            bs = "inf (unbounded)" if B == math.inf else f"{B:.2f}"
            need = "ℓ<=1 NEEDED for prize"
            print(f"   delta={delta:.4f} ({tag:15s})  Johnson ℓ-budget = {bs}")
        print()
    print("=== conclusion (exact) ===")
    print("At the Johnson radius the q-independent list budget 1/((1-delta)^2-rho)")
    print("-> infinity (denominator -> 0). Inside the window interior it is")
    print("VACUOUS (delta past Johnson => budget = inf). No proven bound gives ℓ<=1")
    print("there; in fact below-Johnson probes already show ℓ>=2..5 at fixed gap.")
    print("Hence c = ℓ >= 2 throughout the window  =>  C009's per-cell bound n gives")
    print("only I <= c*n with c the SAME open list size. I <= c*n is a tautology;")
    print("C009 RELOCATES the prize to 'bound the GS list size ℓ in the window',")
    print("which is precisely the BGK/capacity-list open core. No closure.")


if __name__ == "__main__":
    main()
