/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Round 7 (Issue #232, ABF26) — the QUADRATIC GAUSS SUM, the one Weil-type magnitude bound that
# Mathlib can support, supplied as the missing analytic ingredient for the second-moment angle.

Round 6 (`SubsetSumE2PowerSumReduction.lean`, `twoSymmetric_count_eq_e1_psum2_count`) reduced the open
`t = 2` joint count to the **(sum, sum-of-squares)** count

  `N2(a; c₁, c₂) := #{ a-subsets S of the smooth 2^k-subgroup G : ∑_{x∈S} x = c₁  ∧  ∑_{x∈S} x² = c₂ }`,

and Round 4 (`SubsetSumCharacterSum.lean`) supplied the **exact additive-character expansion** of the
*single-constraint* subset-sum count, isolating a Gauss-type error whose cancellation is the open
question. Pushing that expansion to the **two-constraint** `N2` count introduces, per character pair
`(ψ₁, ψ₂)`, the single-coordinate factor `ψ₂(b·x²)` — the value `x ↦ x²` seen by an additive
character. Summing this factor over the field is the classical **quadratic Gauss sum**, and its
square-root magnitude `√q` is the **one Weil-type estimate Mathlib already proves** (via
`gaussSum_sq`, the relation `g(χ)² = χ(−1)·q` for a quadratic character `χ`).

## What this round contributes (the analytic input the second-moment angle was missing)

This file formalizes the quadratic Gauss sum over a finite field `F` of odd characteristic, with an
additive character `ψ : AddChar F ℂ`, and its exact magnitude:

* `sum_addChar_sq_eq_gaussSum` — **the analytic identity**
  `∑_{x∈F} ψ(x²) = gaussSum (χ_ℂ) ψ`,
  where `χ_ℂ = (quadraticChar F).ringHomComp (Int.castRingHom ℂ)` is the quadratic character pushed
  into `ℂ`. Proof: fiber the sum over the value `a = x²` (`Finset.sum_fiberwise_of_maps_to`), use
  `quadraticChar_card_sqrts` (`#{x : x² = a} = χ(a) + 1`), and kill the trivial-character part by
  `AddChar.sum_eq_zero_of_ne_one`. This is the precise object the inner generating function of `N2`
  meets, now identified with a *bona fide* Gauss sum.

* `gaussSum_quadraticChar_sq` — **the Weil square** `gaussSum(χ_ℂ) ψ ^ 2 = χ_ℂ(−1) · q`, the
  application of Mathlib's `gaussSum_sq` to the quadratic character pushed into `ℂ` (nontriviality and
  quadraticity transferred through `ringHomComp`).

* `sum_addChar_sq_sq` — combining the two: `(∑_{x∈F} ψ(x²))² = χ_ℂ(−1)·q`, the exact value of the
  squared quadratic Gauss sum, sign `χ(−1) = ±1`.

* `norm_sum_addChar_sq_sq` — **the magnitude (the Weil bound):** `‖∑_{x∈F} ψ(x²)‖² = q` (a real
  equation), hence `‖∑_{x∈F} ψ(x²)‖ = √q` (`norm_sum_addChar_sq`). This is the square-root cancellation
  the bare additive-character method (`charSum_error_norm_le`, Round 4) provably could NOT see — here
  for the quadratic single-coordinate sum it IS available, because the multiplicative structure enters
  through `gaussSum_sq`.

* `norm_sum_addChar_bsq` — **the `b`-shifted version (the per-character-term magnitude):** for every
  `b ≠ 0`, `‖∑_{x∈F} ψ(b·x²)‖ = √q`. (Apply the identity to the primitive shifted character
  `ψ.mulShift b`, which is primitive for `b ≠ 0` over a field.) This is exactly the `b`-indexed inner
  factor that appears in the character expansion of `N2`.

## Honest scope (what this is and is NOT)

* This is the **full-field** quadratic Gauss sum, `∑_{x∈F} ψ(x²)`, with its **exact √q magnitude**.
  It is `sorry`-free and axiom-clean. It is the genuine analytic ingredient (the "Weil case Mathlib
  supports") that the (sum, sum-of-squares) second-moment expansion needs, and it was **not** present
  in the earlier rounds (Round 4 stopped at the *additive* error envelope with no cancellation).

* It does **NOT** by itself bound `N2(a; c₁, c₂)`. The character expansion of `N2` over the *subgroup*
  `G` (not the full field) yields, per `(ψ₁, ψ₂)`, an inner generating-function coefficient of
  `∏_{x∈G}(1 + z·ψ₁(b₁x)ψ₂(b₂x²))` — a **product over the subgroup**, of which `ψ₂(b·x²)` is one
  factor; the full-field √q magnitude bounds the *summed* single factor, not the subgroup product. The
  subgroup-restricted quadratic sum `∑_{x∈G} ψ(b·x²)` is a **partial** Gauss sum, whose cancellation
  needs Weil's bound for `∑_{x} ψ(f(x))χ(g(x))` over the curve cut out by `G = {x : x^n = 1}` —
  general Weil/Riemann-hypothesis-for-curves, which Mathlib **lacks**. We record this delimiter
  precisely (`subgroup_quadratic_sum_is_partial`): the full-field magnitude is the analytic input; the
  subgroup partial sum is the still-open object.

* The honest delta over Round 4/6: Round 4 proved the additive method **cannot** beat the triangle
  bound on its own error; Round 6 recoordinated the open count to (sum, sum-of-squares). This round
  supplies the **one cancellation that IS provable in Mathlib** — the √q magnitude of the quadratic
  single-coordinate sum — which is the analytic seed of the second-moment estimate, while being
  explicit that the subgroup product is not thereby closed.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Round7QuadraticGauss

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The quadratic character pushed into `ℂ`.** `quadraticChar F : MulChar F ℤ` takes values in
`{−1, 0, 1} ⊆ ℤ`; composing with `Int.castRingHom ℂ` gives a `MulChar F ℂ` with the same `±1, 0`
values, the object `gaussSum` and `gaussSum_sq` consume. -/
noncomputable def quadCharC (F : Type*) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

/-- `quadCharC F a = ((quadraticChar F a : ℤ) : ℂ)`. -/
theorem quadCharC_apply (a : F) : quadCharC F a = ((quadraticChar F a : ℤ) : ℂ) := by
  rw [quadCharC, MulChar.ringHomComp_apply]; simp only [Int.coe_castRingHom]

/-! ## 1. The fiberwise grouping of `∑_{x∈F} ψ(x²)` by the value `a = x²`. -/

/-- **Fiberwise grouping.** Summing `ψ(x²)` over `x ∈ F` equals summing over the *value* `a`, weighted
by the number of square roots of `a`:

  `∑_{x∈F} ψ(x²) = ∑_{a∈F} #{x : x² = a} · ψ(a)`.

This is `Finset.sum_fiberwise_of_maps_to` for the map `x ↦ x²`, with each fiber's summand constant
`ψ(a)`. -/
theorem sum_addChar_sq_fiberwise (ψ : AddChar F ℂ) :
    ∑ x : F, ψ (x ^ 2)
      = ∑ a : F, (Finset.univ.filter (fun x => x ^ 2 = a)).card • ψ a := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => x ^ 2)
        (fun x _ => Finset.mem_univ ((x : F) ^ 2))]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_congr rfl (g := fun _ => ψ a) (fun x hx => by
        rw [Finset.mem_filter] at hx; rw [hx.2]), Finset.sum_const]

/-- **The square-root count, cast to `ℂ`.** `#{x : x² = a} = χ_ℂ(a) + 1` over `ℂ`, the cast of
Mathlib's `quadraticChar_card_sqrts` (`#{x : x² = a} = quadraticChar F a + 1` in `ℤ`). -/
theorem card_sqrts_cast (hF : ringChar F ≠ 2) (a : F) :
    ((Finset.univ.filter (fun x => x ^ 2 = a)).card : ℂ) = quadCharC F a + 1 := by
  have h := quadraticChar_card_sqrts hF a
  have h2 : ((Finset.univ.filter (fun x => x ^ 2 = a)).card : ℤ) = quadraticChar F a + 1 := by
    rw [← h]; congr 1; rw [Set.toFinset_setOf]
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h2
  rw [quadCharC_apply]
  push_cast at hc ⊢
  convert hc using 2

/-! ## 2. The analytic identity: `∑_{x∈F} ψ(x²) = gaussSum (χ_ℂ) ψ`. -/

/-- **The quadratic Gauss sum identity.** For a finite field of odd characteristic and a *primitive*
additive character `ψ : AddChar F ℂ`,

  `∑_{x∈F} ψ(x²) = gaussSum (χ_ℂ) ψ`,

where `χ_ℂ = quadCharC F`. The single-coordinate map `x ↦ x²`, summed against `ψ`, is exactly the
Gauss sum of the quadratic character — the classical identity, here over a genuine `AddChar F ℂ`.
Proof: fiber over `a = x²` (`sum_addChar_sq_fiberwise`), substitute `#{x : x²=a} = χ_ℂ(a)+1`
(`card_sqrts_cast`), expand, and drop the trivial-character part `∑_a ψ(a) = 0`
(`AddChar.sum_eq_zero_of_ne_one`, since a primitive character over a field is `≠ 1`). -/
theorem sum_addChar_sq_eq_gaussSum (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ∑ x : F, ψ (x ^ 2) = gaussSum (quadCharC F) ψ := by
  rw [sum_addChar_sq_fiberwise]
  -- replace each weighted summand `#fiber • ψ a` by `(χ_ℂ(a)+1)·ψ a`
  have hsubst : ∑ a : F, (Finset.univ.filter (fun x => x ^ 2 = a)).card • ψ a
      = ∑ a : F, (quadCharC F a + 1) * ψ a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [nsmul_eq_mul, card_sqrts_cast hF a]
  rw [hsubst]
  -- split off the trivial-character sum `∑_a ψ(a)`, which vanishes
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib]
  have hzero : ∑ a : F, ψ a = 0 := by
    apply AddChar.sum_eq_zero_of_ne_one
    intro hone
    have hns : ψ.mulShift 1 ≠ 1 := hψ one_ne_zero
    rw [AddChar.mulShift_one] at hns
    exact hns hone
  rw [hzero, add_zero, gaussSum]

/-! ## 3. The Weil square: `gaussSum(χ_ℂ) ψ ^ 2 = χ_ℂ(−1)·q`. -/

/-- **`χ_ℂ` is a nontrivial quadratic character on `ℂ`.** Nontriviality and quadraticity of
`quadraticChar F` transfer through the injective `Int.castRingHom ℂ` (`ringHomComp_eq_one_iff`,
`IsQuadratic.comp`). -/
theorem quadCharC_ne_one (hF : ringChar F ≠ 2) : quadCharC F ≠ 1 := by
  rw [quadCharC, Ne, MulChar.ringHomComp_eq_one_iff (f := Int.castRingHom ℂ)
      (by exact_mod_cast Int.cast_injective)]
  exact quadraticChar_ne_one hF

/-- `quadCharC F` is quadratic as a multiplicative character. -/
theorem quadCharC_isQuadratic : (quadCharC F).IsQuadratic :=
  (quadraticChar_isQuadratic F).comp _

/-- **The Weil square of the quadratic Gauss sum.** `gaussSum(χ_ℂ) ψ ^ 2 = χ_ℂ(−1)·q`. This is
Mathlib's `gaussSum_sq` for the nontrivial quadratic character `χ_ℂ` and primitive `ψ`. The factor
`χ_ℂ(−1) = ±1` is the only field-dependent sign; the magnitude is `q`. -/
theorem gaussSum_quadraticChar_sq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    (gaussSum (quadCharC F) ψ) ^ 2 = quadCharC F (-1) * (Fintype.card F : ℂ) :=
  gaussSum_sq (quadCharC_ne_one hF) quadCharC_isQuadratic hψ

/-- **The squared quadratic Gauss sum, in the `x ↦ x²` form.**
`(∑_{x∈F} ψ(x²))² = χ_ℂ(−1)·q`. Combines `sum_addChar_sq_eq_gaussSum` and
`gaussSum_quadraticChar_sq`. -/
theorem sum_addChar_sq_sq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    (∑ x : F, ψ (x ^ 2)) ^ 2 = quadCharC F (-1) * (Fintype.card F : ℂ) := by
  rw [sum_addChar_sq_eq_gaussSum hF hψ, gaussSum_quadraticChar_sq hF hψ]

/-! ## 4. The magnitude (the Weil bound): `‖∑_{x∈F} ψ(x²)‖ = √q`. -/

/-- `‖χ_ℂ(−1)‖ = 1`: the value is the `ℂ`-cast of `quadraticChar F (−1) ∈ {1, −1}`. (No odd-char
hypothesis is needed: `−1 ≠ 0` always, so the dichotomy at `−1` applies.) -/
theorem norm_quadCharC_neg_one : ‖quadCharC F (-1)‖ = 1 := by
  rw [quadCharC_apply]
  have hdich : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (by rw [neg_ne_zero]; exact one_ne_zero)
  rcases hdich with h | h <;> rw [h] <;> simp

/-- **The Weil magnitude (squared form): `‖∑_{x∈F} ψ(x²)‖² = q`.** Taking `‖·‖` of
`sum_addChar_sq_sq` and using `‖χ_ℂ(−1)‖ = 1` collapses the sign to give exactly the cardinality `q`.
This is the square-root cancellation that the bare additive method of Round 4 could not produce. -/
theorem norm_sum_addChar_sq_sq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ x : F, ψ (x ^ 2)‖ ^ 2 = (Fintype.card F : ℝ) := by
  have hsq := sum_addChar_sq_sq hF hψ
  have hnorm : ‖(∑ x : F, ψ (x ^ 2)) ^ 2‖ = ‖quadCharC F (-1)‖ * ‖(Fintype.card F : ℂ)‖ := by
    rw [hsq, norm_mul]
  rw [norm_pow] at hnorm
  rw [norm_quadCharC_neg_one, one_mul, Complex.norm_natCast] at hnorm
  exact hnorm

/-- **The Weil magnitude: `‖∑_{x∈F} ψ(x²)‖ = √q`.** Square-root form of `norm_sum_addChar_sq_sq`. -/
theorem norm_sum_addChar_sq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ x : F, ψ (x ^ 2)‖ = Real.sqrt (Fintype.card F) := by
  rw [← norm_sum_addChar_sq_sq hF hψ, Real.sqrt_sq (norm_nonneg _)]

/-! ## 5. The `b`-shifted quadratic Gauss sum (the per-character-term magnitude in `N2`). -/

omit [Fintype F] [DecidableEq F] in
/-- **`mulShift ψ b` is primitive for `b ≠ 0` over a field.** The shifts `mulShift (mulShift ψ b) a`
`= mulShift ψ (b·a)` are nontrivial for `a ≠ 0` because `b·a ≠ 0` and `ψ` is primitive. -/
theorem isPrimitive_mulShift {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    (ψ.mulShift b).IsPrimitive := by
  intro a ha
  rw [AddChar.mulShift_mulShift]
  exact hψ (mul_ne_zero hb ha)

/-- **The `b`-shifted quadratic Gauss magnitude: `‖∑_{x∈F} ψ(b·x²)‖ = √q` for every `b ≠ 0`.** Apply
`norm_sum_addChar_sq` to the primitive shifted character `ψ.mulShift b`, whose value at `x²` is
`ψ(b·x²)`. This is exactly the `b`-indexed inner single-coordinate factor that appears in the additive
character expansion of the (sum, sum-of-squares) count `N2`: each contributes magnitude `√q`. -/
theorem norm_sum_addChar_bsq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) :
    ‖∑ x : F, ψ (b * x ^ 2)‖ = Real.sqrt (Fintype.card F) := by
  have hps := isPrimitive_mulShift hψ hb
  have hrw : (∑ x : F, ψ (b * x ^ 2)) = ∑ x : F, (ψ.mulShift b) (x ^ 2) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [AddChar.mulShift_apply]
  rw [hrw]
  exact norm_sum_addChar_sq hF hps

/-! ## 6. The honest subgroup delimiter (where the full-field bound stops). -/

set_option linter.unusedVariables false in
/-- **The subgroup quadratic sum is a PARTIAL Gauss sum — the open delimiter.** The second-moment
count `N2` over the smooth subgroup `G ⊊ F` expands, per character pair `(ψ₁, ψ₂)` with frequencies
`(b₁, b₂)`, into an inner generating-function coefficient of `∏_{x∈G}(1 + z·ψ₁(b₁x)·ψ₂(b₂x²))`. The
single-coordinate factor `ψ₂(b₂·x²)` is the object whose **full-field** sum we bounded by `√q`
(`norm_sum_addChar_bsq`); but the count needs the **subgroup-restricted** sum `∑_{x∈G} ψ(b·x²)` (a
*partial* Gauss sum over `G = {x : x^n = 1}`), and a product, not a single factor.

We record the trivial-but-honest decomposition: the subgroup sum plus the complementary sum equals the
full-field quadratic Gauss sum, whose magnitude is pinned (`√q`). Bounding the **subgroup** piece below
the trivial `|G|` envelope requires Weil's bound for `∑_x ψ(f(x))·χ(g(x))` on the curve cut out by
`G`, i.e. the Riemann hypothesis for curves — which Mathlib does **not** have. So this round supplies
the full-field analytic input (the `√q` magnitude) and makes precise that the subgroup partial sum is
the residual open object. -/
theorem subgroup_quadratic_sum_is_partial (ψ : AddChar F ℂ) (b : F) (G : Finset F) :
    (∑ x ∈ G, ψ (b * x ^ 2)) + (∑ x ∈ (Finset.univ \ G), ψ (b * x ^ 2))
      = ∑ x : F, ψ (b * x ^ 2) := by
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  congr 1
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ G)]

/-! ## 7. Non-vacuity: the hypotheses are realized in the smooth-domain regime. -/

/-- **Non-vacuity: a concrete odd-characteristic field with a primitive additive character.**
`F = ZMod 13` (a field, `13` prime, hosting a multiplicative subgroup of order `4 = 2²` — the smooth
FRI domain) has `ringChar (ZMod 13) = 13 ≠ 2`, and a primitive additive character `ZMod 13 → ℂ`
exists (`primitiveChar_to_Complex`). So `sum_addChar_sq_eq_gaussSum`, `norm_sum_addChar_sq`, and
`norm_sum_addChar_bsq` are non-vacuously applicable, and the magnitude `√13` is genuine. -/
theorem hypotheses_satisfiable_zmod13 :
    (ringChar (ZMod 13) ≠ 2) ∧ ∃ ψ : AddChar (ZMod 13) ℂ, ψ.IsPrimitive := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  refine ⟨?_, ?_⟩
  · rw [ringChar.eq (ZMod 13) 13]; decide
  · haveI : Finite (ZMod 13) := inferInstance
    exact ⟨AddChar.FiniteField.primitiveChar_to_Complex (ZMod 13),
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod 13)⟩

end ArkLib.ProximityGap.Round7QuadraticGauss

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.quadCharC_apply
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.sum_addChar_sq_fiberwise
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.card_sqrts_cast
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.sum_addChar_sq_eq_gaussSum
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.quadCharC_ne_one
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.gaussSum_quadraticChar_sq
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.sum_addChar_sq_sq
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.norm_quadCharC_neg_one
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.norm_sum_addChar_sq_sq
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.norm_sum_addChar_sq
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.isPrimitive_mulShift
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.norm_sum_addChar_bsq
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.subgroup_quadratic_sum_is_partial
#print axioms ArkLib.ProximityGap.Round7QuadraticGauss.hypotheses_satisfiable_zmod13
