/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Ring

set_option linter.style.longLine false

/-!
# Subgroup QUADRATIC Gauss-sum second moment, exactly, with NO Weil bound (Issue #232, ABF26).

This extends `SubgroupGaussSumSecondMoment.lean` (the *linear* subgroup Gauss sum
`η_b = ∑_{y∈G} ψ(b·y)`) to the **quadratic** subgroup sum `ζ_b = ∑_{x∈G} ψ(b·x²)`, which is the
single-coordinate object inside the prize-deciding *mixed* statistic `(∑x, ∑x²)` of the
moment-collision tower (`MomentCollisionTower`/`Spectral`/`LocalFactor`). Like the linear case, the
**second moment** over all frequencies is *fully provable elementarily* — by additive-character
orthogonality (Parseval), with **no** Weil / RH-for-curves input:

> `subgroup_quadratic_gaussSum_secondMoment`:
> `∑_{b∈F} ‖∑_{x∈G} ψ(b·x²)‖² = q · #{(x',x) ∈ G×G : x'² = x²}`.

The right-hand `#{(x',x) ∈ G×G : x'² = x²}` is the **square-collision count**, the quadratic analogue
of the linear diagonal `#{(y',y) : y' = y} = |G|`. It is *not* `|G|` and *not* `|G.image (·²)|`: a
genuine off-diagonal contribution survives because `x ↦ x²` is not injective. (Concretely, in odd
characteristic `x'² = x²  ↔  x' = ±x`; for a multiplicative subgroup `G` closed under negation — e.g.
any even-order `2^k` smooth FRI subgroup, which contains `−1` — the map is exactly `2`-to-`1`, so the
collision count is `2|G|` and the typical quadratic subgroup sum has size `√(2|G|)`, still far below
the full-field `√q`.)

## Honest scope

This controls the quadratic subgroup Gauss sum in **L²/average** — exactly the regime that decides
average-case anti-concentration of the collision count — while leaving the **per-frequency worst
case** (the deep-interior pin, which needs Weil's character-sum bound = RH for curves) open. It does
**not** prove any `√q`-strength per-frequency bound and does **not** advance the open core of #232
(`advancesOpenCore = false`). All `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
- A. Weil, *On some exponential sums*, PNAS 1948 (the per-frequency `√q` bound, NOT used here).
-/

open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupQuadraticSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic subgroup Gauss sum at frequency `b`: `ζ_b = ∑_{x∈G} ψ(b·x²)`. -/
noncomputable def zeta (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℂ := ∑ x ∈ G, ψ (b * x ^ 2)

/-- **The quadratic subgroup Gauss-sum second moment, exactly.** No Weil bound — pure
additive-character orthogonality (`AddChar.sum_mulShift`): expanding `‖ζ_b‖² = ζ_b · conj ζ_b` into a
double sum over `(x, x') ∈ G × G` and summing over `b` collapses each pair to `q · [x'² = x²]`, giving

  `∑_b ‖ζ_b‖² = q · ∑_{x'∈G} ∑_{x∈G} [x'² = x²]`,

the `q` times the **square-collision count** of `G`. (Contrast the linear case, where the collision
condition `x' = x` is diagonal and the count is exactly `|G|`.) -/
theorem subgroup_quadratic_gaussSum_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) :
    ∑ b : F, ‖zeta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * ∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℝ) else 0) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  -- Step 1: `ζ_b · conj ζ_b = ‖ζ_b‖²`.
  have hnorm : ∀ b : F, zeta ψ G b * (starRingEnd ℂ) (zeta ψ G b)
      = ((‖zeta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b; rw [RCLike.mul_conj]; norm_cast
  -- conj of a character value: `conj (ψ a) = ψ (-a)`.
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- Step 2: the complex second moment, collapsed by orthogonality.
  have hcomplex : (∑ b : F, zeta ψ G b * (starRingEnd ℂ) (zeta ψ G b))
      = (Fintype.card F : ℂ) * ∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℂ) else 0) := by
    calc ∑ b : F, zeta ψ G b * (starRingEnd ℂ) (zeta ψ G b)
        = ∑ b : F, ∑ x' ∈ G, ∑ x ∈ G, ψ (b * (x' ^ 2 - x ^ 2)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have hconjzeta : (starRingEnd ℂ) (zeta ψ G b) = ∑ x ∈ G, ψ (-(b * x ^ 2)) := by
            rw [zeta, map_sum]; exact Finset.sum_congr rfl (fun x _ => hconj (b * x ^ 2))
          have hL : zeta ψ G b = ∑ x ∈ G, ψ (b * x ^ 2) := rfl
          rw [hconjzeta, hL, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun x' _ => ?_)
          refine Finset.sum_congr rfl (fun x _ => ?_)
          have harg : b * x' ^ 2 + -(b * x ^ 2) = b * (x' ^ 2 - x ^ 2) := by ring
          rw [← AddChar.map_add_eq_mul, harg]
      _ = ∑ x' ∈ G, ∑ x ∈ G, ∑ b : F, ψ (b * (x' ^ 2 - x ^ 2)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun x' _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun x' _ => ?_)
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [AddChar.sum_mulShift (x' ^ 2 - x ^ 2) hψ]
          simp [sub_eq_zero]
      _ = (Fintype.card F : ℂ) * ∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℂ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x' _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [mul_ite, mul_one, mul_zero]
  -- Bridge: the complex collision count is the cast of the real one (structural, no α-mismatch).
  have hbridge : (∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℂ) else 0))
      = ((∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
  -- Step 3: cast the complex identity back to the real second moment.
  have hcast : ((∑ b : F, ‖zeta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * ∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℂ) else 0) := by
    rw [Complex.ofReal_sum, ← hcomplex]
    exact Finset.sum_congr rfl (fun b _ => (hnorm b).symm)
  rw [hbridge] at hcast
  have hreal : ((∑ b : F, ‖zeta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ)
          * ∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-- **The quadratic subgroup Gauss sum vanishes on average at the full-field scale.** The L²-average
of `‖ζ_b‖²` over the `q` frequencies equals the average square-collision count, `≤ |G|²/q`. The point
(mirroring the linear case): the *typical* quadratic subgroup sum is far below the full-field `√q`,
so any improvement must come from a per-frequency *worst-case* bound — which is exactly the Weil input
this development does not have. We record the average identity in its raw exact form. -/
theorem subgroup_quadratic_gaussSum_l2_average {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (∑ b : F, ‖zeta ψ G b‖ ^ 2) / (Fintype.card F : ℝ)
      = ∑ x' ∈ G, ∑ x ∈ G, (if x' ^ 2 = x ^ 2 then (1 : ℝ) else 0) := by
  rw [subgroup_quadratic_gaussSum_secondMoment hψ G, mul_comm, mul_div_assoc,
    div_self (by exact_mod_cast hq.ne'), mul_one]

end ArkLib.ProximityGap.SubgroupQuadraticSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupQuadraticSecondMoment.subgroup_quadratic_gaussSum_secondMoment
#print axioms ArkLib.ProximityGap.SubgroupQuadraticSecondMoment.subgroup_quadratic_gaussSum_l2_average
