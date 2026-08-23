/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QuadraticGaussSumMagnitude

/-!
# Round 8 (Issue #232, ABF26) — COMPLETING THE SQUARE: the mixed linear–quadratic exponential sum
# reduces to the pure quadratic Gauss sum, with the same `√q` magnitude (the SEAM B algebraic bridge).

Round 7 (`QuadraticGaussSumMagnitude.lean`, `norm_sum_addChar_bsq`) pinned the magnitude of the
**pure** quadratic single-coordinate sum `‖∑_{x∈F} ψ(b·x²)‖ = √q` (the one Weil-type estimate Mathlib
supports, via `gaussSum_sq`). But the additive-character expansion of the `(sum, sum-of-squares)`
count `N2` (`SubsetSumSecondMomentCollision.lean`, `N2_secondMoment_eq_collisionCount`) does **not**
produce the pure quadratic frequency `ψ(b₂x²)` per character pair — it produces the **mixed**
linear–quadratic frequency

  `∑_{x∈F} ψ(b₁·x + b₂·x²)`,

where `b₁` comes from the first (linear, `∑x`) constraint and `b₂` from the second (quadratic,
`∑x²`) constraint. This round supplies the **algebraic bridge** that turns that mixed sum into the
pure quadratic one, by **completing the square**.

## What this round contributes — the complete-the-square reduction (full field, fully provable)

For `b₂ ≠ 0` in a field of odd characteristic, the substitution `y = x + b₁/(2b₂)` (a *bijection* of
`F`, `Equiv.addRight`) turns the mixed quadratic `b₁x + b₂x²` into the pure quadratic `b₂y²` shifted
by the constant `−b₁²/(4b₂)`:

  `b₁·x + b₂·x² = b₂·(x + b₁/(2b₂))² − b₁²/(4b₂)`              (`complete_the_square_poly`).

Summing over the field and reindexing by the translation bijection gives the **frequency reduction**

  `∑_{x∈F} ψ(b₁·x + b₂·x²) = ψ(−b₁²/(4b₂)) · ∑_{y∈F} ψ(b₂·y²)`   (`sum_addChar_mixed_eq_const_mul`),

a clean product of a unit-modulus constant `ψ(−b₁²/(4b₂))` (an additive-character value, `‖·‖ = 1`)
times the **pure** quadratic Gauss sum. Taking norms and feeding `norm_sum_addChar_bsq` yields the
headline magnitude:

  `‖∑_{x∈F} ψ(b₁·x + b₂·x²)‖ = √q`   for every `b₂ ≠ 0`           (`norm_sum_addChar_mixed`).

So the **mixed** per-character-term, exactly the inner factor that appears in the character expansion
of `N2`, has the same `√q` magnitude as the pure quadratic Gauss sum — the linear part contributes
only a unit-modulus phase. This is the precise object the second-moment (SEAM B) angle meets.

## Honest scope (what this is and is NOT)

* This is the **full-field** reduction `∑_{x∈F} ψ(b₁x + b₂x²) = ψ(−b₁²/(4b₂))·∑_{y∈F} ψ(b₂y²)`,
  with the **exact** `√q` magnitude. It is `sorry`-free and axiom-clean, and it is *fully* provable:
  completing the square is an algebraic identity plus a translation-invariance reindexing of a sum
  over a finite field — **no** subgroup restriction, **no** Weil/Riemann-hypothesis-for-curves input.
  It removes the *linear* frequency from the analysis cleanly.

* It does **NOT** by itself bound `collisionCount` / `N2`. As in Round 7, the count needs the sum over
  the **subgroup** `G ⊊ F`, not the full field; the complete-the-square reduction is valid only for
  the *full-field* sum (the translation `x ↦ x + b₁/(2b₂)` does **not** preserve `G`). The honest
  delta over Round 7 is: Round 7 supplied the pure quadratic `√q`; this round shows the *mixed*
  linear–quadratic frequency reduces to it (full field), so the entire per-character full-field inner
  factor of `N2` has magnitude `√q`. The residual open object remains the **subgroup-restricted**
  mixed sum `∑_{x∈G} ψ(b₁x + b₂x²)` (a partial sum, no complete-the-square reindex available because
  `G` is not translation-invariant), which still needs Weil for curves — recorded precisely in
  `subgroup_mixed_sum_is_partial`.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Round8CompleteSquare

open ArkLib.ProximityGap.Round7QuadraticGauss

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 0. The unit-modulus of an additive-character value (a phase). -/

omit [DecidableEq F] in
/-- **An additive-character value has modulus `1`.** Over a finite field `F` (positive
characteristic) every value `ψ a : ℂ` of an additive character is a root of unity, hence `‖ψ a‖ = 1`.
This is the fact that the complete-the-square constant `ψ(−b₁²/(4b₂))` is a pure phase and drops out
of the magnitude. (`val_mem_rootsOfUnity` + `Complex.norm_eq_one_of_mem_rootsOfUnity`.) -/
theorem norm_addChar_apply (ψ : AddChar F ℂ) (a : F) : ‖ψ a‖ = 1 := by
  have hR : 0 < ringChar F := by
    have := CharP.ringChar_ne_zero_of_finite F
    omega
  have H := Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.val_mem_rootsOfUnity a hR)
  rwa [IsUnit.unit_spec] at H

/-! ## 1. The algebraic complete-the-square identity (no characters yet). -/

omit [Fintype F] [DecidableEq F] in
/-- **The complete-the-square polynomial identity.** For `b₂ ≠ 0` (so `2·b₂` is a unit when
`char F ≠ 2`) and every `x ∈ F`,

  `b₁·x + b₂·x² = b₂·(x + b₁/(2·b₂))² − b₁²/(4·b₂)`.

Pure field algebra: expand the right side and cancel using `2·b₂ ≠ 0`, `4·b₂ ≠ 0`. This is the
algebraic seed of the frequency reduction — it rewrites the mixed quadratic `b₁x + b₂x²` as a pure
square in the shifted variable `x + b₁/(2b₂)` plus a constant. -/
theorem complete_the_square_poly (h2 : (2 : F) ≠ 0) {b₁ b₂ : F} (hb₂ : b₂ ≠ 0) (x : F) :
    b₁ * x + b₂ * x ^ 2 = b₂ * (x + b₁ / (2 * b₂)) ^ 2 - b₁ ^ 2 / (4 * b₂) := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by ring
    rw [this]; exact mul_ne_zero h2 h2
  have h2b₂ : (2 : F) * b₂ ≠ 0 := mul_ne_zero h2 hb₂
  have h4b₂ : (4 : F) * b₂ ≠ 0 := mul_ne_zero h4 hb₂
  field_simp
  ring

/-! ## 2. The frequency reduction: the mixed sum = constant · pure quadratic Gauss sum. -/

omit [DecidableEq F] in
/-- **The translation reindexing.** For any `c : F`, summing a function `f` of `x + c` over the field
equals summing `f` over the field (the translation `x ↦ x + c` is a bijection of `F`,
`Equiv.addRight c`). We use it with `f y = ψ(b₂·y² − b₁²/(4b₂))` and `c = b₁/(2b₂)` to absorb the
shift introduced by completing the square. -/
theorem sum_translate (c : F) (f : F → ℂ) :
    ∑ x : F, f (x + c) = ∑ y : F, f y :=
  Fintype.sum_equiv (Equiv.addRight c) (fun x => f (x + c)) f (fun x => by
    rw [Equiv.coe_addRight])

omit [DecidableEq F] in
/-- **The mixed linear–quadratic sum equals `ψ(−b₁²/(4b₂))` times the pure quadratic Gauss sum.**
For `b₂ ≠ 0` over a field of odd characteristic,

  `∑_{x∈F} ψ(b₁·x + b₂·x²) = ψ(−b₁²/(4·b₂)) · ∑_{y∈F} ψ(b₂·y²)`.

Proof: rewrite each summand by `complete_the_square_poly`, so `ψ(b₁x + b₂x²) = ψ(b₂(x+c)² − d)` with
`c = b₁/(2b₂)`, `d = b₁²/(4b₂)`; split off the constant via `map_add_eq_mul` (`ψ(u − d) = ψ(u)·ψ(−d)`)
and pull `ψ(−d)` out of the sum; finally reindex `x ↦ x + c` by the translation bijection
(`sum_translate`) to land on the pure quadratic sum `∑_y ψ(b₂y²)`. The constant `ψ(−b₁²/(4b₂))` is an
additive-character value, of modulus `1`: the linear part contributes only a phase. -/
theorem sum_addChar_mixed_eq_const_mul (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    {b₁ b₂ : F} (hb₂ : b₂ ≠ 0) :
    ∑ x : F, ψ (b₁ * x + b₂ * x ^ 2)
      = ψ (-(b₁ ^ 2 / (4 * b₂))) * ∑ y : F, ψ (b₂ * y ^ 2) := by
  set c : F := b₁ / (2 * b₂) with hc
  set d : F := b₁ ^ 2 / (4 * b₂) with hd
  -- Step 1: complete the square inside each summand.
  have hstep1 : ∑ x : F, ψ (b₁ * x + b₂ * x ^ 2)
      = ∑ x : F, ψ (b₂ * (x + c) ^ 2 - d) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [complete_the_square_poly h2 hb₂ x]
  rw [hstep1]
  -- Step 2: split off the additive constant `−d`: `ψ(u − d) = ψ(u)·ψ(−d)`.
  have hstep2 : ∀ x : F, ψ (b₂ * (x + c) ^ 2 - d) = ψ (b₂ * (x + c) ^ 2) * ψ (-d) := by
    intro x
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  simp_rw [hstep2]
  -- Step 3: pull the constant `ψ(−d)` out of the sum.
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  -- Step 4: reindex `x ↦ x + c` (translation bijection) to the pure quadratic sum.
  exact sum_translate c (fun y => ψ (b₂ * y ^ 2))

/-! ## 3. The headline magnitude: the mixed sum has the same `√q` magnitude as the Gauss sum. -/

/-- **The mixed quadratic Gauss magnitude: `‖∑_{x∈F} ψ(b₁·x + b₂·x²)‖ = √q` for every `b₂ ≠ 0`.**
Taking norms of `sum_addChar_mixed_eq_const_mul`: the constant `ψ(−b₁²/(4b₂))` has modulus `1` (any
additive-character value on a finite field is a root of unity, `norm = 1`,
`norm_addChar_apply`), so the magnitude of the mixed sum equals the magnitude of the pure quadratic
Gauss sum, which is `√q` by `norm_sum_addChar_bsq` (Round 7). Thus the **mixed** linear–quadratic
per-character term — exactly the inner factor in the additive-character expansion of the
`(sum, sum-of-squares)` count `N2` — carries the same `√q` cancellation as the pure quadratic case:
the linear constraint contributes only a unit-modulus phase. -/
theorem norm_sum_addChar_mixed (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (b₁ : F) {b₂ : F} (hb₂ : b₂ ≠ 0) :
    ‖∑ x : F, ψ (b₁ * x + b₂ * x ^ 2)‖ = Real.sqrt (Fintype.card F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [sum_addChar_mixed_eq_const_mul h2 ψ hb₂, norm_mul,
    norm_addChar_apply, one_mul, norm_sum_addChar_bsq hF hψ hb₂]

/-! ## 4. The honest subgroup delimiter (where complete-the-square stops). -/

set_option linter.unusedVariables false in
/-- **The subgroup mixed sum is a PARTIAL sum — the open delimiter.** The complete-the-square reduction
`sum_addChar_mixed_eq_const_mul` is valid only for the **full-field** sum: the translation
`x ↦ x + b₁/(2b₂)` is a bijection of `F` but does **not** preserve the multiplicative subgroup
`G ⊊ F`, so the reindexing step is unavailable over `G`. The character expansion of the count `N2`
needs the **subgroup-restricted** mixed sum `∑_{x∈G} ψ(b₁x + b₂x²)`, a *partial* sum; bounding it
below the trivial `|G|` envelope requires Weil's bound for `∑_x ψ(f(x))` on the curve cut out by
`G = {x : x^n = 1}` — the Riemann hypothesis for curves, which Mathlib lacks. We record the
trivial-but-honest decomposition: the subgroup piece plus the complementary piece equals the full-field
mixed sum, whose magnitude is pinned (`√q`, `norm_sum_addChar_mixed`). So this round removes the
*linear* frequency cleanly on the full field, and makes precise that the subgroup partial sum is the
residual open object. -/
theorem subgroup_mixed_sum_is_partial (ψ : AddChar F ℂ) (b₁ b₂ : F) (G : Finset F) :
    (∑ x ∈ G, ψ (b₁ * x + b₂ * x ^ 2))
        + (∑ x ∈ (Finset.univ \ G), ψ (b₁ * x + b₂ * x ^ 2))
      = ∑ x : F, ψ (b₁ * x + b₂ * x ^ 2) := by
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  congr 1
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ G)]

/-! ## 5. Sanity reductions: the mixed sum specializes correctly. -/

omit [DecidableEq F] in
/-- **Specialization `b₁ = 0` recovers the pure quadratic sum exactly.** With no linear term, the
constant `ψ(−0²/(4b₂)) = ψ(0) = 1`, so `∑_x ψ(0·x + b₂x²) = ∑_x ψ(b₂x²)` — a consistency check that
the complete-the-square reduction degenerates to Round 7's pure quadratic sum when the linear
frequency vanishes. -/
theorem sum_addChar_mixed_zero_linear (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    {b₂ : F} (hb₂ : b₂ ≠ 0) :
    ∑ x : F, ψ (0 * x + b₂ * x ^ 2) = ∑ y : F, ψ (b₂ * y ^ 2) := by
  rw [sum_addChar_mixed_eq_const_mul h2 ψ hb₂]
  have : -((0 : F) ^ 2 / (4 * b₂)) = 0 := by
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, neg_zero]
  rw [this, AddChar.map_zero_eq_one, one_mul]

/-! ## 6. Non-vacuity: the hypotheses are realized; the magnitude `√q` is genuine. -/

/-- **Non-vacuity (concrete odd-characteristic field with a primitive additive character).**
`F = ZMod 13` (a field, `13` prime, hosting the smooth FRI order-`4 = 2²` subgroup) has
`ringChar (ZMod 13) = 13 ≠ 2` and `(2 : ZMod 13) ≠ 0`, and a primitive additive character
`ZMod 13 → ℂ` exists. So `sum_addChar_mixed_eq_const_mul` and `norm_sum_addChar_mixed` are
non-vacuously applicable: e.g. with `b₁ = 1`, `b₂ = 1`, the magnitude `‖∑_x ψ(x + x²)‖ = √13` is
genuine. -/
theorem hypotheses_satisfiable_zmod13 :
    (ringChar (ZMod 13) ≠ 2) ∧ ((2 : ZMod 13) ≠ 0)
      ∧ ∃ ψ : AddChar (ZMod 13) ℂ, ψ.IsPrimitive := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ringChar.eq (ZMod 13) 13]; decide
  · decide
  · haveI : Finite (ZMod 13) := inferInstance
    exact ⟨AddChar.FiniteField.primitiveChar_to_Complex (ZMod 13),
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod 13)⟩

end ArkLib.ProximityGap.Round8CompleteSquare

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.norm_addChar_apply
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.complete_the_square_poly
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.sum_translate
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.sum_addChar_mixed_eq_const_mul
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.norm_sum_addChar_mixed
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.subgroup_mixed_sum_is_partial
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.sum_addChar_mixed_zero_linear
#print axioms ArkLib.ProximityGap.Round8CompleteSquare.hypotheses_satisfiable_zmod13
