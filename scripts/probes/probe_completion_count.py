"""Exact-arithmetic check of the completion count at the first sponsor cutoff.

The reciprocal-locator draft bounds the surviving completions of a high-union
pair by the counting step

    L (m (1 - u/L))^3 <= k m^3 + 12 L m^2,

which rearranges to `m ((L-u)^3 - k L^2) <= 12 L^3`.  This probe evaluates the
exact margin at the draft's cutoff and reports the resulting bound on `m`,
together with the weaker `24 t / margin` estimate used in the draft.

Run: `python3 scripts/probes/probe_completion_count.py`
"""

from __future__ import annotations

import sys
from fractions import Fraction as Q

N = 1073741824
D = 536870913
T = 221512374
E0 = 377420252


def main() -> int:
    L = 2 * (E0 - T)
    k = D - E0
    u = T - k
    A = (L - u) ** 3 - k * L * L
    rhs = 12 * L ** 3
    print(f"L = {L}  k = {k}  u = {u}")
    print(f"L - u = {L - u}")
    print(f"margin A = (L-u)^3 - k L^2 = {A}")
    print(f"rhs = 12 L^3 = {rhs}")
    assert A > 0, "margin is not positive"
    # largest m with m A <= 12 L^3
    bound = rhs // A
    print(f"m <= {bound}  (exact ratio {float(Q(rhs, A)):.3f})")
    assert bound * A <= rhs < (bound + 1) * A, "bound is not tight"
    assert bound == 4806, bound
    # the draft's cruder estimate 24 t / margin
    margin = Q(L * (L - u) ** 3, L ** 3) - k
    crude = Q(24 * T, margin)
    print(f"draft margin L(1-u/L)^3 - k = {float(margin):.3f}")
    print(f"draft estimate 24t/margin = {float(crude):.3f}")
    assert bound < crude, "exact bound should be stronger"
    # the third-moment cap is what the geometry has to supply
    print("third-moment cap: sum f^3 <= k m^3 + 12 L m^2")
    return 0


if __name__ == "__main__":
    sys.exit(main())
