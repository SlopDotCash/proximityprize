# Issue #466: the rung-2 production anchor — cyclotomic accident reduction (design + numerics)

Date: 2026-07-11 (UTC). Design note with verified numerics; Lean target claimed as G136.

## The structure (all numerics exact, verified)

For H = μ_n ⊂ ZMod p, n a 2-power (so −1 ∈ H):

1. **The zero-sum plane is the third n².** E₂ counts {x,y}={z,w} pairs (2n²−n) PLUS the
   zero-sum quadruples x+y = z+w = 0 (n²−2n+... ), totalling exactly 3n²−3n when no
   arithmetic accidents occur. Verified: E₂ = 3n²−3n exactly for n=8 at ALL p ∈
   [73, 257] tested — including p = 73..137 BELOW the in-tree Sidon threshold p ≥ 144
   (12^φ(8) = 20736 < p²). The in-tree threshold is far from sharp.
2. **Accidents are 𝔭-divisibility events.** Dividing x+y=z+w by w, nontrivial-beyond-plane
   solutions biject with a+b = c+1 (a,b,c ∈ μ_n) beyond the Mann set. Over ℚ(ζ_{2^k}) the
   4-term vanishing sums of 2-power roots of unity decompose into vanishing PAIRS
   (2-power Mann classification), giving exactly the {x,y}={z,w} and zero-sum families.
   Every OTHER mod-p solution is a nonzero cyclotomic integer a+b−c−1 (height ≤ 4 in every
   embedding) divisible by the degree-1 prime 𝔭 above p. Verified: accidents appear only
   at p = 17, 41 (E₂ = 264, 200) and vanish from p = 73 on, in multiples of n·N.
3. **Production applicability.** v₂(P−1) = 36 for the certified prime P = 2^30(2^128+192)+1
   (computed exactly), so μ_{2^31} ⊂ ZMod P and the reduction applies verbatim at
   production: **the rung-2 anchor holds iff the certified prime divides none of the
   nonzero 4-term μ_{2^30}-sums a+b−c−1** — a pure 𝔭-divisibility statement about
   bounded-height cyclotomic integers, heuristic failure probability ~n³/p ≈ 2^{-68}.

## G136 Lean targets (claimed)

1. Formalize the 2-power Mann classification for 4-term sums (induction on the cyclotomic
   tower ℚ(ζ_{2^k})/ℚ(ζ_{2^{k−1}}), using Mathlib's IsCyclotomicExtension bases).
2. The exact accident law: E₂(μ_n, ZMod p) = 3n²−3n + n·#accidents(p).
3. Corollary: the production rung-2 anchor ⟺ zero accidents at P — replacing the
   astronomically-failing Sidon threshold with the sharp criterion.

Higher anchors t = 3..10 have analogous Mann-type reductions (2t-term 2-power sums also
decompose into pairs), suggesting the ENTIRE anchor zone reduces to 𝔭-divisibility of
finitely many bounded-height cyclotomic values — a new, sharp, per-prime formulation of the
bump wall.

## Honest scope

Design + exact small-scale verification; the Lean formalization is claimed, not landed;
the production divisibility statement is the wall in a new (sharper) form, not a proof.
CORE remains OPEN.
