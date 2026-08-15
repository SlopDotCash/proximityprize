# Issue #466 G136 (part 1): the unit-circle Mann classification — elementary and universal

Date: 2026-07-11 (UTC). `Frontier/_G136UnitCircleMann.lean`, axiom-clean, 0 sorryAx.

## Result

`unit_sum_classification`: for ANY unit-modulus complex a, b, c with a + b = c + 1:

    a = 1  ∨  b = 1  ∨  (c = −1 ∧ b = −a).

Proof is fully elementary — no cyclotomic towers, no Galois theory: conjugating the
equation (conj = inverse on the circle, Mathlib's `Complex.inv_eq_conj`) and clearing
denominators yields `(c+1)(c−ab) = 0`; the branch `c = ab` factors the original as
`(a−1)(b−1) = 0`.

## Significance

1. The characteristic-zero solution set of the rung-2 equation is EXACTLY the three
   families of part 0 (identity, swap, zero-sum plane) — for roots of unity of EVERY
   order simultaneously, not just 2-powers. The planned tower induction was unnecessary;
   this is stronger and simpler than the classical route.
2. Combined with part 0's count: over ℂ (equivalently over the cyclotomic field), the
   rung-2 energy of μ_n (even n) is EXACTLY 3n²−3n. Every mod-p excess is a reduction
   accident — part 2 (the accident law over ZMod p via the ring-hom transfer from
   ℤ[μ_n] ⊂ ℂ... formally: solutions in ZMod p lift to root-of-unity triples; those
   whose char-0 lift solves the equation are the three families; the rest have
   a+b−c−1 ≠ 0 in ℂ but ≡ 0 mod 𝔭) and part 3 (the sharp production criterion) remain.

CORE remains OPEN.
