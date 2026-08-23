/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Issue #232 (ABF26) — the SPECTRAL HOME of the moment-collision scalar:
# a Plancherel identity exhibiting the exact Weil target.

Round 7 reduced the prize to the single scalar `collisionCount = ∑_c N2(c)²` and flagged the missing
ingredient: a **subgroup-restricted (partial) quadratic character sum**, i.e. a Weil-on-curves
estimate that Mathlib does not have. The fleet's `MixedGaussSumDiagonal` / `MixedGaussSumCompleteSquare`
supply the **full-field** ground-set factor `‖∑_{x∈F} ψ(b₁x + b₂x²)‖ = √q`; what is still missing is
the bridge from those per-character factors to the collision count itself.

This file supplies that bridge: the **Plancherel/spectral identity** for the collision count. For
*any* finite-abelian-group-valued statistic `stat : Finset F → A` (`A = F` is the subset-sum count;
`A = F × F` is the prize's `(∑x, ∑x²)` count; `A = Fin t → F` is the depth-`t` moment tower), with
Fourier coefficient `T ψ := ∑_{S} ψ (stat S)` over the dual group `AddChar A ℂ`,

  `collision · |A| = ∑_{ψ : AddChar A ℂ} ‖T ψ‖²`,

and isolating the trivial-character **main term** `T 0 = C(|G|, a)`:

  `collision · |A| = (C(|G|, a))² + ∑_{ψ ≠ 0} ‖T ψ‖²`.

The off-diagonal `∑_{ψ ≠ 0} ‖T ψ‖²` is **exactly** the open "Weil" magnitude. Each `T ψ` is a subset
character sum `∑_{|S|=a} ∏_{x∈S} χ(x)` (an elementary symmetric polynomial in the per-element
character values `χ(x) = ψ(stat x)`); for the smooth `2^k`-subgroup the per-character factor is the
subgroup-restricted partial quadratic sum the fleet's Gauss-sum work targets. This identity is the
precise spectral statement of where Weil-on-curves enters; we do **not** bound the off-diagonal
(Mathlib lacks the Riemann-hypothesis-for-curves input), but we pin its exact home.

## Key Mathlib inputs
`AddChar.sum_apply_eq_ite` (second orthogonality over the dual group) and `AddChar.card_eq`
(Pontryagin duality, `card (AddChar A ℂ) = card A`), from `Mathlib/Analysis/Fourier/FiniteAbelian/`.

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Exact spectral identity +
isolated main term; the off-diagonal is left as the open magnitude.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

namespace ArkLib.ProximityGap.MomentCollisionSpectral

open Finset Complex
open scoped BigOperators

variable {F : Type*} [DecidableEq F]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Statistic-collision count for an arbitrary finite-abelian-group-valued statistic. -/
noncomputable def collision (G : Finset F) (a : ℕ) (stat : Finset F → A) : ℕ :=
  ((G.powersetCard a ×ˢ G.powersetCard a).filter (fun p => stat p.1 = stat p.2)).card

/-- The Fourier coefficient `T ψ = ∑_S ψ (stat S)`. -/
noncomputable def charSum (G : Finset F) (a : ℕ) (stat : Finset F → A) (ψ : AddChar A ℂ) : ℂ :=
  ∑ S ∈ G.powersetCard a, ψ (stat S)

/-- Second orthogonality relation, restated: `∑_{ψ} ψ y = |A| · [y = 0]`. -/
theorem sum_char_eq_ite (y : A) :
    ∑ ψ : AddChar A ℂ, ψ y = if y = 0 then (Fintype.card A : ℂ) else 0 :=
  AddChar.sum_apply_eq_ite y

/-- The indicator `[y = 0]` as the normalised character sum. -/
theorem indicator_eq_inv_card_sum_char (y : A) :
    (if y = 0 then (1 : ℂ) else 0) = (Fintype.card A : ℂ)⁻¹ * ∑ ψ : AddChar A ℂ, ψ y := by
  rw [sum_char_eq_ite]
  have hq : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α := A))
  split_ifs with h
  · field_simp
  · simp

/-- `normSq (T ψ) = ∑_{S, S'} ψ (stat S' - stat S)`. -/
theorem normSq_charSum_eq_double_sum
    (G : Finset F) (a : ℕ) (stat : Finset F → A) (ψ : AddChar A ℂ) :
    (Complex.normSq (charSum G a stat ψ) : ℂ)
      = ∑ S ∈ G.powersetCard a, ∑ S' ∈ G.powersetCard a, ψ (stat S' - stat S) := by
  rw [Complex.normSq_eq_conj_mul_self]
  unfold charSum
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro S _
  refine Finset.sum_congr rfl ?_
  intro S' _
  rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
  congr 1
  abel

/-- **Plancherel / character expansion of the collision count.**
`collision · |A| = ∑_{ψ : AddChar A ℂ} ‖T ψ‖²`. The LHS is the combinatorial collision count scaled
by `|A|`; the RHS is the spectral energy of the Fourier coefficients. -/
theorem plancherel_collision (G : Finset F) (a : ℕ) (stat : Finset F → A) :
    (collision G a stat : ℂ) * (Fintype.card A : ℂ)
      = ∑ ψ : AddChar A ℂ, (Complex.normSq (charSum G a stat ψ) : ℂ) := by
  have key :
      (∑ ψ : AddChar A ℂ, (Complex.normSq (charSum G a stat ψ) : ℂ))
        = ∑ S ∈ G.powersetCard a, ∑ S' ∈ G.powersetCard a,
            (if stat S = stat S' then (Fintype.card A : ℂ) else 0) := by
    simp_rw [normSq_charSum_eq_double_sum G a stat]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro S' _
    rw [AddChar.sum_apply_eq_ite]
    simp only [sub_eq_zero]
    rw [if_congr (eq_comm (a := stat S') (b := stat S)) rfl rfl]
  rw [key, collision, Finset.natCast_card_filter (R := ℂ), Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro S _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro S' _
  split_ifs <;> ring

/-- The trivial character gives the main term `T 0 = C(|G|, a)`. -/
theorem charSum_zero (G : Finset F) (a : ℕ) (stat : Finset F → A) :
    charSum G a stat (0 : AddChar A ℂ) = ((G.powersetCard a).card : ℂ) := by
  unfold charSum; simp [AddChar.zero_apply]

theorem normSq_charSum_zero (G : Finset F) (a : ℕ) (stat : Finset F → A) :
    Complex.normSq (charSum G a stat (0 : AddChar A ℂ)) = ((G.powersetCard a).card : ℝ) ^ 2 := by
  rw [charSum_zero, Complex.normSq_eq_norm_sq, Complex.norm_natCast]

/-- **Plancherel with the main (trivial-character) term isolated.**
`collision · |A| = (C(|G|,a))² + ∑_{ψ ≠ 0} ‖T ψ‖²`. The off-diagonal `∑_{ψ ≠ 0} ‖T ψ‖²` is the
genuinely open "Weil" magnitude — for the smooth `2^k`-subgroup `(∑x, ∑x²)` statistic it is a
subgroup-restricted (partial) quadratic character sum, which Mathlib's Weil-on-curves gap leaves
open. This identity is the exact spectral home of the prize-deciding scalar. -/
theorem plancherel_collision_main_term (G : Finset F) (a : ℕ) (stat : Finset F → A) :
    (collision G a stat : ℂ) * (Fintype.card A : ℂ)
      = (((G.powersetCard a).card : ℝ) ^ 2 : ℂ)
        + ∑ ψ ∈ (Finset.univ.erase (0 : AddChar A ℂ)),
            (Complex.normSq (charSum G a stat ψ) : ℂ) := by
  rw [plancherel_collision, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : AddChar A ℂ)),
    add_comm]
  congr 1
  rw [normSq_charSum_zero]; push_cast; ring

end ArkLib.ProximityGap.MomentCollisionSpectral

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MomentCollisionSpectral.plancherel_collision
#print axioms ArkLib.ProximityGap.MomentCollisionSpectral.plancherel_collision_main_term
#print axioms ArkLib.ProximityGap.MomentCollisionSpectral.sum_char_eq_ite
#print axioms ArkLib.ProximityGap.MomentCollisionSpectral.indicator_eq_inv_card_sum_char
#print axioms ArkLib.ProximityGap.MomentCollisionSpectral.normSq_charSum_eq_double_sum
