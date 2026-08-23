/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QuadraticGaussSumMagnitude
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumSecondMomentCollision
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Round 8 (Issue #232, ABF26) — SEAM B: the FULL-FIELD MIXED linear+quadratic Gauss sum
# `∑_{x∈F} ψ(b₁·x + b₂·x²)` has magnitude `√q`, the FIRST genuine *magnitude* input to the
# collision count `M2 = collisionCount` that controls the prize dichotomy.

Round 7 narrowed the `§7` list-decoding open core (the prize counterexample door) to the single
scalar `M2 = collisionCount G a` of `SubsetSumSecondMomentCollision.lean`:

* `M2 = ∑_{(c₁,c₂)} N2(c₁,c₂)²` (`N2_secondMoment_eq_collisionCount`), and
* small `M2 ≈ C(n,a)²/q²` ⟺ anti-concentration ⟺ **prize survives**;
  large `M2 ≳ C(n,a)²` ⟺ concentration ⟺ a `q`-independent super-poly list ⟺ **disproof**
  (`choose_sq_le_support_mul_collisionCount`).

The natural analytic route to `M2` is its **two-dimensional additive-character expansion**: by
orthogonality (`AddChar.sum_mulShift`),

  `M2 = (1/q²) ∑_{b₁,b₂ ∈ F} | ∑_{a-subsets S} ψ(b₁·∑_S x + b₂·∑_S x²) |²`,

and the inner sum *factors over the ground set* into a generating function in which the single
ground-set coordinate seen by the characters is the **mixed linear+quadratic** value
`x ↦ b₁·x + b₂·x²`. Summing that one coordinate over `F` is the classical **mixed Gauss sum**

  `S(b₁,b₂) := ∑_{x∈F} ψ(b₁·x + b₂·x²)`,

whose magnitude is the Weil input the whole expansion rests on.

## What this round contributes (the FIRST magnitude handle for the `M2` expansion)

Round 7 (`QuadraticGaussSumMagnitude.lean`) proved the **pure** quadratic case
`‖∑_{x} ψ(b·x²)‖ = √q` (`norm_sum_addChar_bsq`). This round supplies the **mixed** case by *completing
the square*: over a field of odd characteristic, for every `b₂ ≠ 0` and every `b₁`,

  `b₁·x + b₂·x²  =  b₂·(x + c)²  −  b₂·c²`,   where `c := b₁·(2·b₂)⁻¹`,

so translating `x ↦ x − c` (a bijection of `F`) gives the **exact identity**

  `S(b₁,b₂)  =  ψ(−b₂·c²) · ∑_{y∈F} ψ(b₂·y²)`               (`mixedGaussSum_eq_shift`),

a unit-modulus phase `ψ(−b₂·c²)` times the pure quadratic Gauss sum. Taking norms and feeding
Round 7's `norm_sum_addChar_bsq`:

  `‖∑_{x∈F} ψ(b₁·x + b₂·x²)‖  =  √q`                          (`norm_mixedGaussSum`).

This is the genuine new brick: the **first actual magnitude bound** on the mixed exponential sum that
sits at the heart of the `M2` character expansion — the analytic ingredient the second-moment angle
was missing on its *second* (linear) frequency. We also record the diagonal/off-diagonal split of the
expansion abstractly: the diagonal `b₁ = b₂ = 0` term is `C(n,a)²`, the field-independent main term
(`mixedGaussSum_diagonal`, here as the pure value `S(0,0) = q`, the ground-set count), while every
off-diagonal *quadratic* frequency `b₂ ≠ 0` contributes a ground-set factor of controlled magnitude
`√q` per the new bound.

## Honest scope (what this is and is NOT)

* `norm_mixedGaussSum` (`‖∑_{x∈F} ψ(b₁x + b₂x²)‖ = √q`, `b₂ ≠ 0`) and the completing-the-square
  identity `mixedGaussSum_eq_shift` are **exact, `sorry`-free, axiom-clean** over a *genuine* finite
  field of odd characteristic. They are the **full-field** mixed Gauss sum — the magnitude handle on
  the second (linear) character frequency that the `M2` expansion needs, and which was absent from all
  earlier rounds (Round 7 had only the *pure* quadratic frequency).
* This does **NOT** bound `M2 = collisionCount` itself, for the same reason Round 7 was honest about:
  the `M2` expansion needs the **subgroup-restricted** mixed sum `∑_{x∈G} ψ(b₁x + b₂x²)` over
  `G = {x : x^n = 1} ⊊ F`, a **partial** Gauss sum whose cancellation below the trivial `|G|` envelope
  requires Weil's bound for `∑_x ψ(f(x))` on the curve cut out by `G` — the Riemann hypothesis for
  curves, which Mathlib lacks. We record the precise delimiter (`subgroup_mixed_sum_is_partial`): the
  full-field magnitude is pinned; the subgroup partial sum is the residual open object.
* The honest delta over Round 7: Round 7 supplied `√q` for the *pure quadratic* single-frequency sum;
  this round supplies `√q` for the *full mixed linear+quadratic* sum (both frequencies active), which
  is the actual per-`(b₁,b₂)` ground-set factor in the `M2` expansion. Plus the abstract diagonal
  isolation `S(0,0) = q` = ground-set size, the seed of the `C(n,a)²` main term. The subgroup vs
  full-field gap is unchanged and remains the open core.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

-- The headline theorems (`norm_mixedGaussSum`, `mixedGaussSum_eq_shift`) genuinely require
-- `[Fintype F] [DecidableEq F]` (the Gauss-sum reindex and `norm_sum_addChar_bsq` need them); we keep
-- them in the shared `variable` block, so a few auxiliary lemmas carry them without using them.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Round8MixedGauss

open ArkLib.ProximityGap.Round7QuadraticGauss

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The mixed linear+quadratic Gauss sum and the completing-the-square algebra. -/

/-- The **mixed linear+quadratic Gauss sum** `S(b₁,b₂) := ∑_{x∈F} ψ(b₁·x + b₂·x²)`, the per-frequency
ground-set factor appearing in the two-dimensional additive-character expansion of the collision
count `M2 = collisionCount G a` over the *full field* `F`. -/
noncomputable def mixedGaussSum (ψ : AddChar F ℂ) (b₁ b₂ : F) : ℂ :=
  ∑ x : F, ψ (b₁ * x + b₂ * x ^ 2)

/-- **The completing-the-square pointwise identity.** For `(2 : F) ≠ 0` and `b₂ ≠ 0`, with
`c := b₁·(2·b₂)⁻¹`, every `x ∈ F` satisfies

  `b₁·x + b₂·x²  =  b₂·(x + c)²  −  b₂·c²`.

This is the elementary completion of the square; `2·b₂ ≠ 0` (odd characteristic, `b₂ ≠ 0`) is what
lets `c` clear the linear term. -/
theorem complete_square_pointwise (h2 : (2 : F) ≠ 0) {b₁ b₂ : F} (hb₂ : b₂ ≠ 0) (x : F) :
    b₁ * x + b₂ * x ^ 2 = b₂ * (x + b₁ * (2 * b₂)⁻¹) ^ 2 - b₂ * (b₁ * (2 * b₂)⁻¹) ^ 2 := by
  have h2b₂ : (2 * b₂) ≠ 0 := mul_ne_zero h2 hb₂
  field_simp
  ring

/-! ## 2. The exact shift identity: `S(b₁,b₂) = ψ(−b₂·c²) · (quadratic Gauss sum)`. -/

/-- **The reindexing translation `x ↦ x − c` is a bijection of `F`.** (Used to absorb the linear
term after completing the square.) -/
theorem add_const_bijective (c : F) : Function.Bijective (fun x : F => x + c) :=
  ⟨fun a b h => by simpa using h, fun y => ⟨y - c, by ring⟩⟩

/-- **The exact completing-the-square shift identity for the mixed Gauss sum.** For `(2 : F) ≠ 0`,
`b₂ ≠ 0`, and any primitive (indeed any) `ψ`, with `c := b₁·(2·b₂)⁻¹`,

  `∑_{x∈F} ψ(b₁·x + b₂·x²)  =  ψ(−b₂·c²) · ∑_{y∈F} ψ(b₂·y²)`.

Proof: rewrite each summand by `complete_square_pointwise` to `ψ(b₂·(x+c)² − b₂·c²)`, split off the
constant `ψ(−b₂·c²)` (additive-character multiplicativity `map_add_eq_mul`), then reindex
`x ↦ x − c` (a bijection, `add_const_bijective`) so the sum becomes `∑_y ψ(b₂·y²)`. The result is a
unit-modulus phase times the pure quadratic Gauss sum of Round 7. -/
theorem mixedGaussSum_eq_shift (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} {b₁ b₂ : F} (hb₂ : b₂ ≠ 0) :
    mixedGaussSum ψ b₁ b₂
      = ψ (-(b₂ * (b₁ * (2 * b₂)⁻¹) ^ 2)) * ∑ y : F, ψ (b₂ * y ^ 2) := by
  classical
  set c : F := b₁ * (2 * b₂)⁻¹ with hc
  unfold mixedGaussSum
  -- Rewrite each summand by completing the square, splitting off the constant phase.
  have hstep : ∀ x : F, ψ (b₁ * x + b₂ * x ^ 2)
      = ψ (-(b₂ * c ^ 2)) * ψ (b₂ * (x + c) ^ 2) := by
    intro x
    rw [complete_square_pointwise h2 hb₂ x]
    rw [show b₂ * (x + c) ^ 2 - b₂ * c ^ 2
          = (-(b₂ * c ^ 2)) + b₂ * (x + c) ^ 2 by ring]
    rw [AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl (fun x _ => hstep x)]
  rw [← Finset.mul_sum]
  congr 1
  -- reindex `x ↦ x + c` so `∑_x ψ(b₂·(x+c)²) = ∑_y ψ(b₂·y²)`.
  exact (add_const_bijective c).sum_comp (fun y => ψ (b₂ * y ^ 2))

/-! ## 3. The magnitude: `‖S(b₁,b₂)‖ = √q` for every `b₂ ≠ 0` (the new full-field Weil input). -/

/-- **The phase `ψ(−b₂·c²)` has unit modulus.** Any additive-character value into `ℂ` is a root of
unity (`AddChar.norm_apply` over a finite group), hence norm `1`. -/
theorem norm_addChar_eq_one (ψ : AddChar F ℂ) (z : F) : ‖ψ z‖ = 1 :=
  ψ.norm_apply z

/-- **The full-field MIXED Gauss-sum magnitude: `‖∑_{x∈F} ψ(b₁·x + b₂·x²)‖ = √q` for every
`b₂ ≠ 0`.** Take norms in `mixedGaussSum_eq_shift`: the phase `ψ(−b₂·c²)` has modulus `1`
(`norm_addChar_eq_one`) and the remaining factor is the pure quadratic Gauss sum, whose magnitude is
`√q` by Round 7's `norm_sum_addChar_bsq`. This is the **mixed** (both-frequencies-active)
single-coordinate Weil input that the two-dimensional `M2` character expansion needs — the brick
Round 7 supplied only for the pure quadratic frequency. -/
theorem norm_mixedGaussSum (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b₁ b₂ : F} (hb₂ : b₂ ≠ 0) :
    ‖mixedGaussSum ψ b₁ b₂‖ = Real.sqrt (Fintype.card F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [mixedGaussSum_eq_shift h2 hb₂, norm_mul, norm_addChar_eq_one, one_mul]
  exact norm_sum_addChar_bsq hF hψ hb₂

/-! ## 4. The diagonal main term of the `M2` expansion: `S(0,0) = q`. -/

/-- **The diagonal frequency `S(0,0) = q`.** At `b₁ = b₂ = 0` every summand is `ψ(0) = 1`, so the
mixed Gauss sum is the ground-set size `q = |F|`. In the two-dimensional character expansion of
`M2 = collisionCount`, the `(b₁,b₂) = (0,0)` term is precisely the field-independent diagonal main
term that produces the `C(n,a)²` floor (`collisionCount_le_choose_sq`,
`choose_sq_le_support_mul_collisionCount`); we isolate its single-coordinate value here. -/
theorem mixedGaussSum_diagonal (ψ : AddChar F ℂ) :
    mixedGaussSum ψ 0 0 = (Fintype.card F : ℂ) := by
  unfold mixedGaussSum
  simp only [zero_mul, add_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-! ## 5. The honest subgroup delimiter (where the full-field bound stops). -/

set_option linter.unusedVariables false in
/-- **The subgroup mixed sum is a PARTIAL Gauss sum — the open delimiter.** The collision count `M2`
over the smooth subgroup `G ⊊ F` expands, per frequency pair `(b₁,b₂)`, into a ground-set
generating-function factor whose summed single coordinate is the **subgroup-restricted** mixed sum
`∑_{x∈G} ψ(b₁·x + b₂·x²)`. The **full-field** mixed sum we just bounded by `√q`
(`norm_mixedGaussSum`); but `M2` needs the *partial* sum over `G = {x : x^n = 1}`. We record the
trivial-but-honest decomposition: the subgroup sum plus the complementary sum equals the full-field
mixed Gauss sum, whose magnitude is pinned (`√q`). Bounding the **subgroup** piece below the trivial
`|G|` envelope requires Weil's bound for `∑_x ψ(f(x))` on the curve cut out by `G` — the Riemann
hypothesis for curves, which Mathlib does **not** have. So this round supplies the full-field analytic
input (the `√q` magnitude of the *mixed* sum) and makes precise that the subgroup partial sum is the
residual open object. -/
theorem subgroup_mixed_sum_is_partial (ψ : AddChar F ℂ) (b₁ b₂ : F) (G : Finset F) :
    (∑ x ∈ G, ψ (b₁ * x + b₂ * x ^ 2)) + (∑ x ∈ (Finset.univ \ G), ψ (b₁ * x + b₂ * x ^ 2))
      = mixedGaussSum ψ b₁ b₂ := by
  unfold mixedGaussSum
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  congr 1
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ G)]

/-! ## 6. Non-vacuity: the hypotheses are realized in the smooth-domain regime. -/

/-- **Non-vacuity: a concrete odd-characteristic field with a primitive additive character.**
`F = ZMod 13` (a field, `13` prime, hosting the order-`4 = 2²` smooth FRI subgroup) has
`ringChar (ZMod 13) = 13 ≠ 2` and a primitive additive character. So `mixedGaussSum_eq_shift` and
`norm_mixedGaussSum` apply non-vacuously: for any `b₂ ≠ 0` the mixed Gauss sum has the genuine
magnitude `√13`. -/
theorem hypotheses_satisfiable_zmod13 :
    (ringChar (ZMod 13) ≠ 2) ∧ ((2 : ZMod 13) ≠ 0) ∧
      ∃ ψ : AddChar (ZMod 13) ℂ, ψ.IsPrimitive := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ringChar.eq (ZMod 13) 13]; decide
  · decide
  · haveI : Finite (ZMod 13) := inferInstance
    exact ⟨AddChar.FiniteField.primitiveChar_to_Complex (ZMod 13),
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod 13)⟩

end ArkLib.ProximityGap.Round8MixedGauss

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8MixedGauss.complete_square_pointwise
#print axioms ArkLib.ProximityGap.Round8MixedGauss.add_const_bijective
#print axioms ArkLib.ProximityGap.Round8MixedGauss.mixedGaussSum_eq_shift
#print axioms ArkLib.ProximityGap.Round8MixedGauss.norm_addChar_eq_one
#print axioms ArkLib.ProximityGap.Round8MixedGauss.norm_mixedGaussSum
#print axioms ArkLib.ProximityGap.Round8MixedGauss.mixedGaussSum_diagonal
#print axioms ArkLib.ProximityGap.Round8MixedGauss.subgroup_mixed_sum_is_partial
#print axioms ArkLib.ProximityGap.Round8MixedGauss.hypotheses_satisfiable_zmod13
