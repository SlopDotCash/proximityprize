/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PolynomialFoldDecomposition

/-!
# The supply fold injection (#389): the polynomial is its fold pair

The supply fold recursion (issue #389) rests on one count fact: the level-`n` supply
**injects** into a pair of half-scale objects via the fold `p ↦ (foldEven p, foldOdd p)`.
This file lands the injectivity backbone, axiom-clean:

* `fold_injective` — `p ↦ (foldEven p, foldOdd p)` is **injective** on `F[X]`: a polynomial
  is determined by its even/odd folds (immediate from `fold_decomposition`). Hence the
  count of any family of polynomials is at most the count of their fold pairs — the
  set-up the supply recursion needs to bound the level-`n` count by a level-`n/2` count.
* `fold_card_le` — over a `DecidableEq` field: for any `Finset` of polynomials, its
  cardinality equals (hence is `≤`) the cardinality of its image under the fold map.

Combined with `fiber_agreement_iff` (a full antipodal-fiber agreement of `p` is a joint
agreement of its fold pair at the folded point), this is the rigorous form of the recursion
inequality `#{p : ≥ f full-fiber agreements} ≤ #{fold pairs jointly agreeing ≥ f}` whose
right side is a half-scale supply. The residual singleton stratum (issue #389 thread) is the
open core; this backbone is unconditional.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
* Issue #389; `PolynomialFoldDecomposition.lean` (the fold engine).
-/

open Polynomial

namespace ArkLib.ProximityGap.PolynomialFold

variable {R : Type*} [CommRing R]

/-- **The fold is injective**: a polynomial is determined by its even and odd folds. -/
theorem fold_injective :
    Function.Injective (fun p : R[X] => (foldEven p, foldOdd p)) := by
  intro p q h
  have he : foldEven p = foldEven q := congrArg Prod.fst h
  have ho : foldOdd p = foldOdd q := congrArg Prod.snd h
  rw [fold_decomposition p, fold_decomposition q, he, ho]

/-- The fold map sends distinct polynomials to distinct pairs, so any finite family of
polynomials has cardinality equal to its fold image — the count backbone of the supply
recursion. -/
theorem fold_card_le [DecidableEq R[X]] (S : Finset R[X]) :
    S.card = (S.image (fun p => (foldEven p, foldOdd p))).card :=
  (Finset.card_image_of_injective S fold_injective).symm

/-! ## Source audit -/

#print axioms fold_injective
#print axioms fold_card_le

end ArkLib.ProximityGap.PolynomialFold
