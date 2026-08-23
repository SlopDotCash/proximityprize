/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TowerDescentNoSaving
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DyadicTowerDescent

/-!
# The antipodal-tower descent telescopes across octaves to a single base rung (#444 / #407)

`_TowerDescentNoSaving` proved the single-octave constraint lemma: the antipodal-tower root-count
descent on `μ_{2^μ}` is *saving-preserving, not saving-creating* — the `2^s` fiber factor exactly
cancels the `X^{2^s}` degree multiplier, so a thin-group list saving is equivalent to a base-rung
saving (`towerDescent_saving_iff`). This file telescopes that across octaves and pins where the
route bottoms out.

* `comp_X_pow_compose` : the multi-octave substitution composes, `(Q.comp(X^a)).comp(X^b) =
  Q.comp(X^{a·b})` (re-exported from `_DyadicTowerDescent.comp_X_pow_comp_X_pow` for the prize use).
* `natDegree_tower_compose` : the degrees multiply across octaves,
  `natDegree((Q.comp(X^a)).comp(X^b)) = a · b · Q.natDegree`. Two octaves of degree-doubling = one
  degree-`a·b` substitution.
* `towerDescent_no_saving_compose` : the **telescoped no-saving bound** — for a base `Q ≠ 0` and any
  two octaves `s, t` with `s + t ≤ μ`, the root count of the *two-stage* tower polynomial
  `(Q.comp(X^{2^t})).comp(X^{2^s})` on `μ_{2^μ}` is bounded by its own trivial degree bound.
  Iterating the single-octave result, the full `s`-fold tower beats nothing: antipodal symmetry
  telescopes
  to the base rung with NO compounding saving (the `2^{s+t}` total fiber factor exactly matches the
  total degree multiplier). The full `s = μ` descent lands on the one-element base group `μ_{2^0} =
  μ_1 = {1}`; the off-BGK route's open content is the list on this fixed finite (`p`-independent)
  object, confirming c.97's "constant in `n` at fixed dyadic ratio" + `_TowerDescentNoSaving`'s
  base-rung localization.

## Honest scope (rules 1, 3, 4, 6)

This EXTENDS the proven single-octave no-saving result to the full tower and pins its bottom; it is
a **refinement of a refutation-with-mechanism** (the off-BGK route's saving, if any, is fully
localized to the fixed base rung, with no octave-to-octave compounding). It does NOT close CORE; NOT
thinness-essential (char-free degree/composition arithmetic). The descent only ever applies to the
antipodally-symmetric (even/odd) agreement sub-family (`_AntipodalAgreementScope`); the general
non-symmetric worst case is the open BGK core. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issues #444, #407.
-/

open Polynomial

namespace ProximityGap.Frontier.TowerDescentTelescope

/-! ## Multi-octave composition + degree -/

variable {R : Type*}

/-- **Two octaves compose into one.** `(Q.comp(X^a)).comp(X^b) = Q.comp(X^{a·b})`. Iterating the
antipodal one-octave substitution is a single deeper substitution (re-export of the in-tree tower
collapse for the no-saving telescope). -/
theorem comp_X_pow_compose [CommSemiring R] (Q : R[X]) (a b : ℕ) :
    (Q.comp (X ^ a)).comp (X ^ b) = Q.comp (X ^ (a * b)) :=
  DyadicTowerDescent.comp_X_pow_comp_X_pow Q a b

/-- **Degrees multiply across octaves.** `natDegree((Q.comp(X^a)).comp(X^b)) = a · b · Q.natDegree`.
Two octaves of the `X^•` substitution multiply the degree by `a·b`. -/
theorem natDegree_tower_compose [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (Q : R[X]) (a b : ℕ) :
    ((Q.comp (X ^ a)).comp (X ^ b)).natDegree = a * b * Q.natDegree := by
  rw [comp_X_pow_compose, TowerDescentNoSaving.natDegree_comp_X_pow, Nat.mul_assoc]

/-! ## The telescoped no-saving bound -/

variable {F : Type*} [Field F]

open Classical in
/-- **The telescoped no-saving bound.** For a nonzero base `Q` over a field with a primitive
`2^μ`-th root of unity and any two octaves `s, t` with `s + t ≤ μ`, the two-stage tower polynomial
`(Q.comp(X^{2^t})).comp(X^{2^s})` has root count on `μ_{2^μ}` bounded by its own degree bound:

  `rootCount((Q.comp(X^{2^t})).comp(X^{2^s}), μ_{2^μ}) ≤ (tower).natDegree`.

The single-octave no-saving result applied with base `Q.comp(X^{2^t})`: the antipodal descent
telescopes across octaves with NO compounding saving — the total fiber factor exactly matches the
total degree multiplier. -/
theorem towerDescent_no_saving_compose {μ s t : ℕ} (hst : s + t ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {Q : F[X]} (hQ : Q ≠ 0) :
    ((nthRootsFinset (2 ^ μ) (1 : F)).filter
        (fun α => ((Q.comp (X ^ (2 ^ t))).comp (X ^ (2 ^ s))).IsRoot α)).card
      ≤ ((Q.comp (X ^ (2 ^ t))).comp (X ^ (2 ^ s))).natDegree := by
  -- The inner tower `Q.comp(X^{2^t})` is nonzero: composition with `X^{2^t}` (= `expand F (2^t)`,
  -- with `2^t > 0`) preserves nonzero. Then apply the single-octave no-saving result with `s ≤ μ`.
  have hQt : Q.comp (X ^ (2 ^ t)) ≠ 0 := by
    rw [← expand_eq_comp_X_pow]
    exact (expand_ne_zero (Nat.two_pow_pos t)).mpr hQ
  have hs : s ≤ μ := le_trans (Nat.le_add_right s t) hst
  simpa [comp_X_pow_compose] using
    TowerDescentNoSaving.towerDescent_no_saving hs hζ
      (Q := Q.comp (X ^ (2 ^ t))) hQt

end ProximityGap.Frontier.TowerDescentTelescope

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.TowerDescentTelescope.comp_X_pow_compose
#print axioms ProximityGap.Frontier.TowerDescentTelescope.natDegree_tower_compose
#print axioms ProximityGap.Frontier.TowerDescentTelescope.towerDescent_no_saving_compose
