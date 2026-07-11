# Issue #466: rung-3 Mann obstruction — the universal route dies at six terms

Date: 2026-07-11 (UTC). Numerical finding with exact witnesses; scopes the G136
extension lane.

## Finding

The rung-2 unit-circle Mann classification (G136 part 1) is ORDER-UNIVERSAL: valid for
arbitrary unit-modulus elements. At rung 3 (a+b+c = d+e+1) this provably fails:
among 12th roots of unity there are 25 cross-irreducible solutions (no term of {a,b,c}
equals any of {d,e,1}), e.g. exponents L = (1,5,9), R = (4,8):

    ζ + ζ⁵ + ζ⁹ = ζ⁴ + ζ⁸ + 1   (both sides are order-3 vanishing triangles: 0 = 0).

These are Mann's odd-order phenomena: vanishing subsums of order-3 roots. For 2-POWER
orders no order-3 elements exist, so such solutions cannot occur — the classical
pair-decomposition (every vanishing sum of 2-power-order roots splits into ±-pairs)
is both NECESSARY (no universal shortcut, per these witnesses) and SUFFICIENT for the
rung-3+ lawful classification at μ_{2^30}.

## Consequence for the lane

The rungs 3–10 extension of the accident programme must formalize the 2-power
pair-decomposition theorem: induction on the tower ℚ(ζ_{2^m})/ℚ(ζ_{2^{m−1}}) with basis
{1, ζ_{2^m}} (Mathlib IsCyclotomicExtension machinery), then transfer to ZMod p as in
the rung-2 chain. No elementary conjugate-trick shortcut exists beyond four terms — do
not spend effort seeking one.

CORE remains OPEN.
