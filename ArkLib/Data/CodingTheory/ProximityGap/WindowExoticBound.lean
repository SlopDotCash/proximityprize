/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowChainStructure

/-!
# The exotic dichotomy and per-witness rigidity (#371, G3 ladder)

Companions to the chain-family kill: the remaining ("exotic") witnesses of a
deep-window bad set are rigidly separated.

* `witness_gamma_injective_poly` — two bad scalars sharing an agreement set
  coincide, now with POLYNOMIAL multipliers (`deg g < deg ℓ₀`): the
  `ℓ₀`-reduction forces `g₁ = g₂`, and the cancellation runs into second-row
  reducedness.  (The per-witness count is ≤ 1 at every window row.)
* `witness_pair_dichotomy` — at slack 1 (`deg g ≤ 1`), two distinct witness
  complements either intersect in ≤ 1 point or share a `(w−1)`-core (and are
  then chain members, killed by `cored_gamma_unique`): the Wronskian
  `g₂m̂₁ − g₁m̂₂ = h·ℓ₀` has `deg h ≤ 1`, and `h = 0` forces the shared core
  through unique factorization.

Together with `cored_gamma_unique` this reduces the slack-1 stratum-G bad
count to `1 + #exotics` with exotics pairwise ≤ 1-intersecting `w`-subsets —
the pair-counting bound caps them at `C(n,2)/C(w,2)` (≤ `w+3`-compatible for
`w ≥ 6`; the small-`w` sharpening is the remaining named target).
Probe record: `probe_nocore.py` — no-core max 3 at (23,11,4), 2 at (67,11,4),
pairwise intersections exactly ≤ 1.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section ExoticBound

variable {dom : Fin n ↪ F} {w : ℕ}
variable {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}

/-- **Per-witness γ-rigidity with polynomial multipliers**: two bad scalars
sharing an agreement set coincide whenever `deg gᵢ < deg ℓ₀`. -/
theorem witness_gamma_injective_poly
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0)
    (hdℓ₀ : 1 ≤ ℓ₀.natDegree) (hdℓ₁ : 1 ≤ ℓ₁.natDegree)
    (hcop₁ : IsCoprime R₁ ℓ₁)
    {γ₁ γ₂ p₁ p₂ : F} {g₁ g₂ : F[X]} {S : Finset (Fin n)}
    (hdg₁ : g₁.natDegree < ℓ₀.natDegree) (hdg₂ : g₂.natDegree < ℓ₀.natDegree)
    (hid₁ : R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁)
      = g₁ * vanishingPoly dom S)
    (hid₂ : R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁)
      = g₂ * vanishingPoly dom S) :
    γ₁ = γ₂ := by
  have hℓ₀ne : ℓ₀ ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hdℓ₀
    omega
  have hsub : (C γ₁ - C γ₂) * (R₁ * ℓ₀) - (C p₁ - C p₂) * (ℓ₀ * ℓ₁)
      = (g₁ - g₂) * vanishingPoly dom S := by
    linear_combination hid₁ - hid₂
  have hdvdg : ℓ₀ ∣ (g₁ - g₂) * vanishingPoly dom S :=
    ⟨(C γ₁ - C γ₂) * R₁ - (C p₁ - C p₂) * ℓ₁, by linear_combination -hsub⟩
  have hgeq : g₁ = g₂ := by
    have h1 : ℓ₀ ∣ g₁ - g₂ :=
      (isCoprime_vanishingPoly dom hG₀ S).dvd_of_dvd_mul_right hdvdg
    by_contra hgne
    have hCne : g₁ - g₂ ≠ 0 := sub_ne_zero.mpr hgne
    have hdeg := Polynomial.natDegree_le_of_dvd h1 hCne
    have hC0 : (g₁ - g₂).natDegree < ℓ₀.natDegree :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdg₁ hdg₂)
    omega
  subst hgeq
  have hsub2 : (C γ₁ - C γ₂) * (R₁ * ℓ₀) - (C p₁ - C p₂) * (ℓ₀ * ℓ₁) = 0 := by
    linear_combination hsub
  have hc : (C γ₁ - C γ₂) * R₁ * ℓ₀ = (C p₁ - C p₂) * ℓ₁ * ℓ₀ := by
    linear_combination hsub2
  have hcancel : (C γ₁ - C γ₂) * R₁ = (C p₁ - C p₂) * ℓ₁ :=
    mul_right_cancel₀ hℓ₀ne hc
  have hdvd₁ : ℓ₁ ∣ (C γ₁ - C γ₂) * R₁ :=
    ⟨C p₁ - C p₂, by linear_combination hcancel⟩
  have h3 : ℓ₁ ∣ C γ₁ - C γ₂ := hcop₁.symm.dvd_of_dvd_mul_right hdvd₁
  by_contra hne
  have hCne : (C γ₁ - C γ₂ : F[X]) ≠ 0 := by
    rw [← C_sub]
    exact C_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hdeg := Polynomial.natDegree_le_of_dvd h3 hCne
  have hC0 : (C γ₁ - C γ₂ : F[X]).natDegree = 0 := by
    rw [← C_sub]
    exact natDegree_C _
  omega

/-- **The slack-1 witness-pair dichotomy**: distinct complements with degree-≤1
multipliers either intersect in at most one point or differ by exactly one
point each from a common `(w−1)`-core. -/
theorem witness_pair_dichotomy
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0) (hdℓ₀ : ℓ₀.natDegree = w) (hw3 : 3 ≤ w)
    {g₁ g₂ : F[X]} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hdg₁ : g₁.natDegree ≤ 1) (hdg₂ : g₂.natDegree ≤ 1)
    {T₁ T₂ : Finset (Fin n)} (hne : T₁ ≠ T₂)
    (hT₁ : T₁.card ≤ w) (hT₂ : T₂.card ≤ w)
    (hcross : ℓ₀ ∣ g₂ * vanishingPoly dom T₁ - g₁ * vanishingPoly dom T₂) :
    (T₁ ∩ T₂).card ≤ 1 ∨ ∃ K : Finset (Fin n), K = T₁ ∩ T₂ ∧
      (T₁ \ K).card ≤ 1 ∧ (T₂ \ K).card ≤ 1 := by
  set Dif := g₂ * vanishingPoly dom T₁ - g₁ * vanishingPoly dom T₂ with hDif
  rcases eq_or_ne Dif 0 with h0 | hne0
  · -- Wronskian zero: unique factorization forces the near-equal shape
    right
    have heq : g₂ * vanishingPoly dom T₁ = g₁ * vanishingPoly dom T₂ :=
      sub_eq_zero.mp (hDif ▸ h0)
    refine ⟨T₁ ∩ T₂, rfl, ?_, ?_⟩
    · -- every point of T₁ off the intersection is a root of g₁
      have hsub : ∀ i ∈ T₁ \ (T₁ ∩ T₂), g₁.eval (dom i) = 0 := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_inter] at hi
        have hiT₁ : i ∈ T₁ := hi.1
        have hiT₂ : i ∉ T₂ := fun h => hi.2 ⟨hi.1, h⟩
        have hev := congrArg (Polynomial.eval (dom i)) heq
        rw [eval_mul, eval_mul, vanishingPoly_eval_eq_zero dom hiT₁,
          mul_zero] at hev
        rcases mul_eq_zero.mp hev.symm with h | h
        · exact h
        · exfalso
          rw [vanishingPoly, eval_prod, Finset.prod_eq_zero_iff] at h
          obtain ⟨j, hj, hij⟩ := h
          simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hij
          exact hiT₂ (dom.injective hij ▸ hj)
      -- g₁ ≠ 0 of degree ≤ 1 has ≤ 1 roots among the embedded points
      by_contra hbig
      push_neg at hbig
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hbig
      have hri := hsub i hi
      have hrj := hsub j hj
      have hdvdi : (X - C (dom i)) ∣ g₁ := by
        rw [Polynomial.dvd_iff_isRoot]
        exact hri
      have hdvdj : (X - C (dom j)) ∣ g₁ := by
        rw [Polynomial.dvd_iff_isRoot]
        exact hrj
      have hcopij : IsCoprime (X - C (dom i)) (X - C (dom j)) :=
        isCoprime_X_sub_C_of_isUnit_sub
          (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
      have hdvdij : (X - C (dom i)) * (X - C (dom j)) ∣ g₁ :=
        hcopij.mul_dvd hdvdi hdvdj
      have hdd := Polynomial.natDegree_le_of_dvd hdvdij hg₁
      rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
        natDegree_X_sub_C, natDegree_X_sub_C] at hdd
      omega
    · -- symmetric for T₂ via g₂
      have hsub : ∀ i ∈ T₂ \ (T₁ ∩ T₂), g₂.eval (dom i) = 0 := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_inter] at hi
        have hiT₂ : i ∈ T₂ := hi.1
        have hiT₁ : i ∉ T₁ := fun h => hi.2 ⟨h, hi.1⟩
        have hev := congrArg (Polynomial.eval (dom i)) heq
        rw [eval_mul, eval_mul, vanishingPoly_eval_eq_zero dom hiT₂,
          mul_zero] at hev
        rcases mul_eq_zero.mp hev with h | h
        · exact h
        · exfalso
          rw [vanishingPoly, eval_prod, Finset.prod_eq_zero_iff] at h
          obtain ⟨j, hj, hij⟩ := h
          simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hij
          exact hiT₁ (dom.injective hij ▸ hj)
      by_contra hbig
      push_neg at hbig
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hbig
      have hri := hsub i hi
      have hrj := hsub j hj
      have hdvdi : (X - C (dom i)) ∣ g₂ := by
        rw [Polynomial.dvd_iff_isRoot]
        exact hri
      have hdvdj : (X - C (dom j)) ∣ g₂ := by
        rw [Polynomial.dvd_iff_isRoot]
        exact hrj
      have hcopij : IsCoprime (X - C (dom i)) (X - C (dom j)) :=
        isCoprime_X_sub_C_of_isUnit_sub
          (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
      have hdvdij : (X - C (dom i)) * (X - C (dom j)) ∣ g₂ :=
        hcopij.mul_dvd hdvdi hdvdj
      have hdd := Polynomial.natDegree_le_of_dvd hdvdij hg₂
      rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
        natDegree_X_sub_C, natDegree_X_sub_C] at hdd
      omega
  · -- Wronskian nonzero: its degree caps the intersection
    left
    obtain ⟨h, hh⟩ := hcross
    have hhne : h ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hh
      exact hne0 (hDif ▸ hh)
    -- every common point is a root of h
    have hroots : ∀ i ∈ T₁ ∩ T₂, h.eval (dom i) = 0 := by
      intro i hi
      rw [Finset.mem_inter] at hi
      have hev := congrArg (Polynomial.eval (dom i)) hh
      rw [eval_sub, eval_mul, eval_mul,
        vanishingPoly_eval_eq_zero dom hi.1,
        vanishingPoly_eval_eq_zero dom hi.2, mul_zero, mul_zero,
        sub_zero, eval_mul] at hev
      rcases mul_eq_zero.mp hev.symm with h | h
      · exfalso
        exact hG₀ i h
      · exact h
    -- deg h ≤ 1
    have hdh : h.natDegree ≤ 1 := by
      have hDd : Dif.natDegree ≤ w + 1 := by
        have e1 : (g₂ * vanishingPoly dom T₁).natDegree ≤ w + 1 := by
          refine le_trans natDegree_mul_le ?_
          rw [vanishingPoly_natDegree]
          omega
        have e2 : (g₁ * vanishingPoly dom T₂).natDegree ≤ w + 1 := by
          refine le_trans natDegree_mul_le ?_
          rw [vanishingPoly_natDegree]
          omega
        rw [hDif]
        exact le_trans (natDegree_sub_le _ _) (max_le e1 e2)
      have hℓ₀ne : ℓ₀ ≠ 0 := fun h0 => by
        rw [h0, natDegree_zero] at hdℓ₀
        omega
      have hmul := Polynomial.natDegree_mul hℓ₀ne hhne
      rw [← hh] at hmul
      rw [hDif] at hmul hDd
      omega
    -- ≤ 1 common points: two would force degree ≥ 2 on h
    by_contra hbig
    push_neg at hbig
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hbig
    have hdvdi : (X - C (dom i)) ∣ h := by
      rw [Polynomial.dvd_iff_isRoot]
      exact hroots i hi
    have hdvdj : (X - C (dom j)) ∣ h := by
      rw [Polynomial.dvd_iff_isRoot]
      exact hroots j hj
    have hcopij : IsCoprime (X - C (dom i)) (X - C (dom j)) :=
      isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    have hdvdij : (X - C (dom i)) * (X - C (dom j)) ∣ h :=
      hcopij.mul_dvd hdvdi hdvdj
    have hdd := Polynomial.natDegree_le_of_dvd hdvdij hhne
    rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
      natDegree_X_sub_C, natDegree_X_sub_C] at hdd
    omega

end ExoticBound

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.witness_gamma_injective_poly
#print axioms ProximityGap.WBPencil.witness_pair_dichotomy
