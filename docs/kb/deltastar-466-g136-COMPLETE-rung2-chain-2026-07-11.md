# Issue #466 G136 COMPLETE: the rung-2 anchor IS the accident tolerance

Date: 2026-07-11 (UTC). `Frontier/_G136LawfulCount.lean` closes the chain. All five G136
files axiom-clean, 0 sorryAx.

## The theorem (fully machine-checked, no interpretive slack)

`rung2_anchor_iff_accidents`: for any multiplicatively closed H ∌ 0 with −1 ∈ H,
#H = 2^30, char ≠ 2, and any q > 2^90:

    q·E₂(H) ≤ 3·q·(2^30)² + (2^30)⁴   ⟺   #accidents(H) ≤ 3

where accidents(H) = {(a,b,c) ∈ H³ : a+b = c+1} minus the three Mann families
{(1,b,b)}, {(a,1,a)}, {(a,−a,−1)}.

Chain: part 2a bijection (E₂ = n·#solutions) → part 2b lawful count (#solutions =
3n−3 + #accidents; overlaps exactly (1,1,1), (1,−1,−1), (−1,1,−1)) → part 3a tolerance
arithmetic (exact ℕ iff) → the pin A ≤ 3. Part 1 (universal unit-circle Mann) certifies
the Mann families are the complete characteristic-zero solution set — the accidents are
genuinely reduction phenomena; part 0 certifies the constant 3 is optimal.

## What this means for δ*

The production rung-2 anchor — one of the ten wall statements of the census tower — has
been converted from a BGK-face character-sum estimate into a FINITE DIOPHANTINE FACT:
"the certified prime P = 2^30·(2^128+192)+1 admits at most three solutions of a+b = c+1
in μ_{2^30} beyond the Mann families." Expected count 2^{-68}. This is a genuinely new
formulation not previously in the campaign: exact, per-prime, zero analytic content
remaining — the arithmetic of one prime.

The same programme (conjugate-trick Mann for 2t-term sums + the analogous bijections)
extends to rungs 3–10, i.e. potentially the ENTIRE bump wall.

## Honest scope

The accident count at the certified primes is not proven (that is the wall, now in
Diophantine form). CORE remains OPEN.
