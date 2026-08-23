/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiber

/-!
# The m=1 deep band: the quartic word's power-sum fibre (#389)

`CubicSupplyExact` characterized the m=0 (cubic) supply as the zero-sum-triple count.  This
file opens the **m = 1 deep band** — the first band the deep-band δ* programme actually uses
— on the additive side: the explainable 4-cores of the monomial word `x⁴` over `rsCode dom 2`
are exactly the 4-subsets on which the first two **power sums** vanish.

* `quartic_explainable_iff_powersum` — for `(2 : F) ≠ 0` and a 4-subset `T`,
  `T` is explainable by the word `x ↦ (dom x)⁴` ⟺ `∑_{i∈T} dom i = 0 ∧ ∑_{i∈T} (dom i)² = 0`.

This is the m=0 → m=1 step of the additive ladder (`∑x = 0` at m=0, `∑x = ∑x² = 0` at m=1),
via `EsymmFiber.explainable_iff_forcedPoly_degree` plus an explicit Vieta/Newton computation.
The power-sum form (rather than the elementary-symmetric form) is the one that bridges to the
in-tree quadratic Gauss-sum machinery `∑_{a∈G} ψ(s·a + t·a²)`: bounding the smooth-domain
count `#{4-subsets : ∑x = ∑x² = 0}` is the m=1 face of the supply wall.
-/

open Finset Polynomial

namespace ProximityGap.EsymmFiber

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The m=1 power-sum characterization**: a 4-subset `T` is an explainable core of the
quartic word `x ↦ (dom x)⁴` over `rsCode dom 2` iff the first two power sums of `dom(T)`
vanish.  Char `≠ 2`. -/
theorem quartic_explainable_iff_powersum (dom : Fin n ↪ F) (h2 : (2 : F) ≠ 0)
    {T : Finset (Fin n)} (hTcard : T.card = 4) :
    (∃ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)), ∀ i ∈ T, c i = (dom i) ^ 4)
      ↔ (∑ i ∈ T, dom i = 0 ∧ ∑ i ∈ T, (dom i) ^ 2 = 0) := by
  classical
  -- instantiate the EsymmFiber lever with W = X^4, k = 2, m = 1
  have hWdeg : (X ^ 4 : Polynomial F).degree = ((2 + 1 + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
  have hT4 : T.card = 2 + 1 + 1 := by omega
  have hlever := explainable_iff_forcedPoly_degree dom (X ^ 4) hWdeg hT4
  -- the word condition `c i = (X^4).eval (dom i)` is `c i = (dom i)^4`
  have hword : (∃ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)),
        ∀ i ∈ T, c i = (X ^ 4 : Polynomial F).eval (dom i))
      ↔ (∃ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)), ∀ i ∈ T, c i = (dom i) ^ 4) := by
    simp only [eval_pow, eval_X]
  rw [hword] at hlever
  rw [hlever]
  -- now compute forcedPoly = X^4 - coreVanish and read its degree
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hTcard
  -- the vanishing polynomial of the four points
  have hCV : coreVanish dom {a, b, c, d}
      = (X - Polynomial.C (dom a)) * (X - Polynomial.C (dom b))
          * (X - Polynomial.C (dom c)) * (X - Polynomial.C (dom d)) := by
    rw [coreVanish, Finset.prod_insert (by simp [hab, hac, had]),
      Finset.prod_insert (by simp [hbc, hbd]), Finset.prod_insert (by simp [hcd]),
      Finset.prod_singleton]
    ring
  have hcoeff : (X ^ 4 : Polynomial F).coeff (2 + 1 + 1) = 1 := by
    rw [show (2 + 1 + 1 : ℕ) = 4 from rfl, coeff_X_pow]; simp
  set s1 := dom a + dom b + dom c + dom d with hs1
  set s2 := dom a*dom b + dom a*dom c + dom a*dom d + dom b*dom c + dom b*dom d + dom c*dom d
    with hs2
  set s3 := dom a*dom b*dom c + dom a*dom b*dom d + dom a*dom c*dom d + dom b*dom c*dom d with hs3
  set s4 := dom a*dom b*dom c*dom d with hs4
  have hFP : forcedPoly dom 2 1 (X ^ 4) {a, b, c, d}
      = Polynomial.C s1 * X ^ 3 - Polynomial.C s2 * X ^ 2
        + Polynomial.C s3 * X - Polynomial.C s4 := by
    rw [forcedPoly, hcoeff, hCV, map_one, one_mul, hs1, hs2, hs3, hs4]
    simp only [map_add, map_mul]
    ring
  rw [hFP]
  have hsumdom : ∑ i ∈ ({a, b, c, d} : Finset (Fin n)), dom i = s1 := by
    rw [Finset.sum_insert (by simp [hab, hac, had]),
      Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_insert (by simp [hcd]),
      Finset.sum_singleton, hs1]
    ring
  have hsumsq : ∑ i ∈ ({a, b, c, d} : Finset (Fin n)), (dom i) ^ 2 = s1^2 - 2*s2 := by
    rw [Finset.sum_insert (by simp [hab, hac, had]),
      Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_insert (by simp [hcd]),
      Finset.sum_singleton, hs1, hs2]
    ring
  rw [hsumdom, hsumsq]
  -- the two relevant coefficients of the explicit forced polynomial
  have hP3 : (Polynomial.C s1 * X ^ 3 - Polynomial.C s2 * X ^ 2
      + Polynomial.C s3 * X - Polynomial.C s4).coeff 3 = s1 := by
    simp [coeff_X_pow]
  have hP2 : (Polynomial.C s1 * X ^ 3 - Polynomial.C s2 * X ^ 2
      + Polynomial.C s3 * X - Polynomial.C s4).coeff 2 = -s2 := by
    simp [coeff_X_pow]
  constructor
  · intro hdeg
    have h3 : s1 = 0 := by
      rw [← hP3]
      exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by norm_num))
    have h2c : -s2 = 0 := by
      rw [← hP2]
      exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by norm_num))
    have hs2zero : s2 = 0 := by linear_combination -h2c
    refine ⟨h3, ?_⟩
    rw [h3, hs2zero]; ring
  · rintro ⟨h1, h2'⟩
    have hs1z : s1 = 0 := h1
    have hs2z : s2 = 0 := by
      have hh : (2 : F) * s2 = 0 := by
        have : s1 ^ 2 - 2 * s2 = 0 := h2'
        rw [hs1z] at this; linear_combination -this
      rcases mul_eq_zero.mp hh with h | h
      · exact absurd h h2
      · exact h
    rw [hs1z, hs2z]
    have hsimp : Polynomial.C (0 : F) * X ^ 3 - Polynomial.C (0 : F) * X ^ 2
        + Polynomial.C s3 * X - Polynomial.C s4
        = Polynomial.C s3 * X + Polynomial.C (-s4) := by
      simp only [map_zero, map_neg]; ring
    rw [hsimp]
    exact lt_of_le_of_lt degree_linear_le (by norm_num)

open Classical in
/-- **The m=1 supply is the power-sum variety count** (the analogue of
`cubicSupply_eq_sumZeroCard`): the number of explainable 4-cores of the quartic word
equals the number of 4-subsets of the domain on which both power sums vanish.  Char `≠ 2`. -/
theorem quartic_supply_eq_powersum_card (dom : Fin n ↪ F) (h2 : (2 : F) ≠ 0) :
    (((Finset.univ : Finset (Fin n)).powersetCard 4).filter
        (fun T => ∃ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)),
          ∀ i ∈ T, c i = (dom i) ^ 4)).card
      = (((Finset.univ : Finset (Fin n)).powersetCard 4).filter
          (fun T => ∑ i ∈ T, dom i = 0 ∧ ∑ i ∈ T, (dom i) ^ 2 = 0)).card := by
  congr 1
  apply Finset.filter_congr
  intro T hT
  rw [quartic_explainable_iff_powersum dom h2
    (Finset.mem_powersetCard.mp hT).2]

end ProximityGap.EsymmFiber
