/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.K2OwnedTriples
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipMultiplicity

/-!
# The k = 2 collinearity-multiplicity theorem

Assembles `owned_triples_card_ge` (the geometric count) with
`badScalars_card_mul_le_ownership` (the engine) and `mcaEvent_owned_tuples`
(witness extraction) into the high-spread half of the k = 2 universal law:
a direction `u₁` of collinearity `≤ ν` has, at every radius `δ ≤ w/n`,

  `#bad · ((n−w)·(n−w−1)·(n−w−ν)) ≤ n³`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- Bridge: the function-tuple owned set has the same cardinality as the
product owned set. -/
theorem owned_pi_card_eq (dom : Fin n ↪ F) (W : Finset (Fin n)) (u₁ : Fin n → F) :
    (Finset.univ.filter (fun t : Fin 3 → Fin n =>
        (∀ a, t a ∈ W) ∧ residual dom 2 t u₁ ≠ 0)).card
      = ((W ×ˢ W ×ˢ W).filter
          (fun p => residual dom 2 ![p.1, p.2.1, p.2.2] u₁ ≠ 0)).card := by
  refine Finset.card_nbij' (fun t => (t 0, t 1, t 2)) (fun p => ![p.1, p.2.1, p.2.2]) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product] at ht ⊢
    obtain ⟨hmem, hres⟩ := ht
    refine ⟨⟨hmem 0, hmem 1, hmem 2⟩, ?_⟩
    have het : ![t 0, t 1, t 2] = t := by funext i; fin_cases i <;> rfl
    rw [het]; exact hres
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product] at hp ⊢
    obtain ⟨⟨ha, hb, hc⟩, hres⟩ := hp
    refine ⟨fun a => ?_, hres⟩
    fin_cases a <;> simp_all
  · intro t ht
    funext i; fin_cases i <;> rfl
  · intro p hp; rfl

open Classical in
/-- **The k = 2 collinearity-multiplicity theorem.** -/
theorem badScalars_card_mul_le_of_collinearity (dom : Fin n ↪ F)
    {w : ℕ} (hw : w ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {ν : ℕ}
    (hν : ∀ i j : Fin n, i ≠ j →
      (Finset.univ.filter (fun c => residual dom 2 ![i, j, c] u₁ = 0)).card ≤ ν) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * ((n - w) * ((n - w) - 1) * ((n - w) - ν))
      ≤ Fintype.card (Fin 3 → Fin n) := by
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) with hbad
  have hch : ∀ γ ∈ bad, ∃ S : Finset (Fin n),
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
      ∀ t : Fin 3 → Fin n, (∀ a, t a ∈ S) →
        residual dom 2 t u₁ ≠ 0 →
        residual dom 2 t u₀ + γ * residual dom 2 t u₁ = 0 := by
    intro γ hγ
    exact mcaEvent_owned_tuples dom (by norm_num) δ (Finset.mem_filter.mp hγ).2
  choose! W hWsz hWprop using hch
  set 𝒯 : F → Finset (Fin 3 → Fin n) := fun γ =>
    Finset.univ.filter (fun t => (∀ a, t a ∈ W γ) ∧ residual dom 2 t u₁ ≠ 0) with h𝒯
  refine badScalars_card_mul_le_ownership dom 2 u₀ u₁ bad _ 𝒯 ?_ ?_
  · -- ownership property
    intro γ hγ t ht
    obtain ⟨htW, htres⟩ := (Finset.mem_filter.mp ht).2
    exact ⟨htres, hWprop γ hγ t htW htres⟩
  · -- ownership size
    intro γ hγ
    -- witness size ≥ n − w
    have hSsz : n - w ≤ (W γ).card := by
      have h1 := hWsz γ hγ
      have h2 : ((n - w : ℕ) : ℝ≥0) ≤ ((W γ).card : ℝ≥0) := by
        have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by rw [Fintype.card_fin]
        calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by rw [Nat.cast_tsub]
          _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
              rw [hcardn] at hδn ⊢; exact tsub_le_tsub_left hδn _
          _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by rw [tsub_mul, one_mul, hcardn]
          _ ≤ ((W γ).card : ℝ≥0) := h1
      exact_mod_cast h2
    -- collinearity on W γ ≤ ν
    have hνW : ∀ i ∈ W γ, ∀ j ∈ W γ, i ≠ j →
        ((W γ).filter (fun c => residual dom 2 ![i, j, c] u₁ = 0)).card ≤ ν := by
      intro i _ j _ hij
      exact le_trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ _))) (hν i j hij)
    -- the geometric count, transported to the function form
    have hcount := owned_triples_card_ge dom (W γ) (u₁ := u₁) (ν := ν) hνW
    have hbridge : (𝒯 γ).card
        = ((W γ ×ˢ W γ ×ˢ W γ).filter
            (fun p => residual dom 2 ![p.1, p.2.1, p.2.2] u₁ ≠ 0)).card := by
      rw [h𝒯]; exact owned_pi_card_eq dom (W γ) u₁
    -- monotonicity: (n−w)(n−w−1)(n−w−ν) ≤ |W γ|(|W γ|−1)(|W γ|−ν)
    have hmono : (n - w) * ((n - w) - 1) * ((n - w) - ν)
        ≤ (W γ).card * ((W γ).card - 1) * ((W γ).card - ν) :=
      Nat.mul_le_mul (Nat.mul_le_mul hSsz (by omega)) (by omega)
    rw [hbridge]
    exact le_trans hmono hcount

end ProximityGap.Ownership

#print axioms ProximityGap.Ownership.owned_pi_card_eq
#print axioms ProximityGap.Ownership.badScalars_card_mul_le_of_collinearity
