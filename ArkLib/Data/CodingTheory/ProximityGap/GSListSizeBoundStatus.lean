/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# GS list-size bound toward Grand Challenge 1 — honest status (issue #141)

**De-larped.** The previous content fabricated a `listSizeBoundedByYDegree_of_breakthrough`
"Breakthrough Synthesis" theorem that took a *false* hypothesis (`YDegreeRootBound degY 0`, which
unfolds to "every finset `L` has `L.card ≤ degY`" since `(0 : F[X][Y]).eval (C 0) = 0` makes its
premise vacuously true) together with a near-vacuous `MultiplicityIntersectionBound`
(`∃ roots, roots ≥ s*k`, satisfiable by `roots := s*k`), and discharged the conclusion with `sorry`.
It proved nothing and had zero consumers.

The genuine list-size bound for the Guruswami–Sudan decoder requires the real factor theorem over
`F(X)` (a nonzero `Q(X,Y)` has at most `deg_Y Q` roots `f(X)` in `F(X)`) plus the multiplicity
intersection count — the open content of `mcaConjecture` (see `GrandChallenge1Proof.lean` for the
honest status). The verified linear-algebra core (interpolant existence) lives in
`GSInterpolationExistence.lean`. No theorem here asserts the bound.
-/
