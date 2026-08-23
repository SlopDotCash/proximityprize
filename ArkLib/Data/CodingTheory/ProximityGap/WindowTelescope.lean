/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowExoticBound

/-!
# The window telescope (#371, G3 ladder): the general-slack pair kill

**`window_pair_telescope`** — at EVERY window row (`k = 1`), two bad scalars
whose witness complements share MORE than `3w − n` points coincide.

The mechanism (probe-confirmed at slack 2, `probe_cf_telescope.py`,
factorization 28/28): take `K := S₁ᶜ ∩ S₂ᶜ` — the extras `Eᵢ = Sᵢᶜ ∖ K` are
then DISJOINT — and run:
* the cross-relation `ℓ₀ ∣ m_K·(g₂·m_{E₁} − g₁·m_{E₂})` peels `m_K`;
* when `|K| > 3w − n` the degree budget forces exactness
  `g₂·m_{E₁} = g₁·m_{E₂}`, and disjointness factors `gᵢ = m_{Eᵢ}·cᵢ`;
* the identities telescope: `Φᵢ·m_K = cᵢ·m_D` (cancel `m_{Eᵢ}`);
* subtracting, `ℓ₀ ∣ c₁ − c₂` with degree `< w` forces `c₁ = c₂`, hence
  `Φ₁ = Φ₂`, and second-row reducedness pins `γ₁ = γ₂`.

Consequence (assembled separately): the witness complements of DISTINCT bad
scalars pairwise share at most `D_def = 3w − n` points at every window row —
the slack-1 dichotomy (`≤ 1` at `n + 1 = 3w`) is the first instance — and the
bad count is capped by the `(D_def+1)`-subset Fisher bound.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Vanishing polynomials multiply over disjoint unions. -/
theorem vanishingPoly_union_disjoint (dom : Fin n ↪ F) {A B : Finset (Fin n)}
    (h : Disjoint A B) :
    vanishingPoly dom (A ∪ B) = vanishingPoly dom A * vanishingPoly dom B := by
  rw [vanishingPoly, vanishingPoly, vanishingPoly, ← Finset.prod_union h]

/-- Vanishing polynomials of disjoint sets are coprime. -/
theorem isCoprime_vanishingPoly_disjoint (dom : Fin n ↪ F)
    {A B : Finset (Fin n)} (h : Disjoint A B) :
    IsCoprime (vanishingPoly dom A) (vanishingPoly dom B) := by
  rw [vanishingPoly, vanishingPoly]
  refine IsCoprime.prod_left fun i hi => IsCoprime.prod_right fun j hj => ?_
  refine isCoprime_X_sub_C_of_isUnit_sub (Ne.isUnit (sub_ne_zero.mpr ?_))
  intro hij
  have hieq : i = j := dom.injective hij
  subst hieq
  exact (Finset.disjoint_left.mp h) hi hj

section Telescope

variable {dom : Fin n ↪ F} {w : ℕ}
variable {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}

/-- **THE WINDOW TELESCOPE.**  Two bad scalars whose witness complements share
more than `3w − n` points coincide — at every window row. -/
theorem window_pair_telescope
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0) (hdℓ₀ : ℓ₀.natDegree = w)
    (hw : 1 ≤ w) (hn2w : 2 * w < n)
    (hdℓ₁ : 1 ≤ ℓ₁.natDegree)
    (hcop₀ : IsCoprime R₀ ℓ₀) (hcop₁ : IsCoprime R₁ ℓ₁) (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {γ₁ γ₂ p₁ p₂ : F} {g₁ g₂ : F[X]} {S₁ S₂ : Finset (Fin n)}
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hS₁ : (n - w : ℕ) ≤ S₁.card) (hS₂ : (n - w : ℕ) ≤ S₂.card)
    (hbud₁ : g₁.natDegree + S₁.card ≤ 2 * w)
    (hbud₂ : g₂.natDegree + S₂.card ≤ 2 * w)
    (hid₁ : R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁)
      = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁)
      = g₂ * vanishingPoly dom S₂)
    (hK : 3 * w < n + ((S₁ᶜ ∩ S₂ᶜ : Finset (Fin n))).card) :
    γ₁ = γ₂ := by
  classical
  set K : Finset (Fin n) := S₁ᶜ ∩ S₂ᶜ with hKdef
  set E₁ : Finset (Fin n) := S₁ᶜ \ K with hE₁def
  set E₂ : Finset (Fin n) := S₂ᶜ \ K with hE₂def
  have hℓ₀ne : ℓ₀ ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hdℓ₀
    omega
  have hKsub₁ : K ⊆ S₁ᶜ := Finset.inter_subset_left
  have hKsub₂ : K ⊆ S₂ᶜ := Finset.inter_subset_right
  have hdisj₁ : Disjoint K E₁ := Finset.disjoint_sdiff
  have hdisj₂ : Disjoint K E₂ := Finset.disjoint_sdiff
  have hdisjE : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h1 := Finset.mem_sdiff.mp hx₁
    have h2 := Finset.mem_sdiff.mp hx₂
    exact h1.2 (Finset.mem_inter.mpr ⟨h1.1, h2.1⟩)
  have hT₁eq : K ∪ E₁ = S₁ᶜ := Finset.union_sdiff_of_subset hKsub₁
  have hT₂eq : K ∪ E₂ = S₂ᶜ := Finset.union_sdiff_of_subset hKsub₂
  have hm₁ : vanishingPoly dom S₁ᶜ
      = vanishingPoly dom K * vanishingPoly dom E₁ := by
    rw [← hT₁eq, vanishingPoly_union_disjoint dom hdisj₁]
  have hm₂ : vanishingPoly dom S₂ᶜ
      = vanishingPoly dom K * vanishingPoly dom E₂ := by
    rw [← hT₂eq, vanishingPoly_union_disjoint dom hdisj₂]
  -- size bookkeeping
  have hcard₁ : (S₁ᶜ : Finset (Fin n)).card = n - S₁.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hcard₂ : (S₂ᶜ : Finset (Fin n)).card = n - S₂.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hE₁card : E₁.card = (S₁ᶜ : Finset (Fin n)).card - K.card := by
    have h : (S₁ᶜ \ K).card = (S₁ᶜ : Finset (Fin n)).card - (K ∩ S₁ᶜ).card :=
      Finset.card_sdiff
    rw [Finset.inter_eq_left.mpr hKsub₁] at h
    exact h
  have hE₂card : E₂.card = (S₂ᶜ : Finset (Fin n)).card - K.card := by
    have h : (S₂ᶜ \ K).card = (S₂ᶜ : Finset (Fin n)).card - (K ∩ S₂ᶜ).card :=
      Finset.card_sdiff
    rw [Finset.inter_eq_left.mpr hKsub₂] at h
    exact h
  have hScard₁ : S₁.card ≤ n := by
    have := Finset.card_le_univ S₁
    rwa [Fintype.card_fin] at this
  have hScard₂ : S₂.card ≤ n := by
    have := Finset.card_le_univ S₂
    rwa [Fintype.card_fin] at this
  have hKle₁ : K.card ≤ (S₁ᶜ : Finset (Fin n)).card := Finset.card_le_card hKsub₁
  have hKle₂ : K.card ≤ (S₂ᶜ : Finset (Fin n)).card := Finset.card_le_card hKsub₂
  -- the cross relation, m_K peeled
  have hcross := witness_cross_dvd hG₀ hcop₀ hcopℓ hid₁ hid₂
  rw [hm₁, hm₂] at hcross
  have hcross' : ℓ₀ ∣ (g₂ * vanishingPoly dom E₁ - g₁ * vanishingPoly dom E₂)
      * vanishingPoly dom K := by
    obtain ⟨c, hc⟩ := hcross
    exact ⟨c, by linear_combination hc⟩
  have hdvdDif : ℓ₀ ∣ g₂ * vanishingPoly dom E₁ - g₁ * vanishingPoly dom E₂ :=
    (isCoprime_vanishingPoly dom hG₀ K).dvd_of_dvd_mul_right hcross'
  -- exactness from the degree budget
  have hzero : g₂ * vanishingPoly dom E₁ - g₁ * vanishingPoly dom E₂ = 0 := by
    by_contra hne0
    have hdeg := Polynomial.natDegree_le_of_dvd hdvdDif hne0
    have e1 : (g₂ * vanishingPoly dom E₁).natDegree < w := by
      refine lt_of_le_of_lt natDegree_mul_le ?_
      rw [vanishingPoly_natDegree]
      omega
    have e2 : (g₁ * vanishingPoly dom E₂).natDegree < w := by
      refine lt_of_le_of_lt natDegree_mul_le ?_
      rw [vanishingPoly_natDegree]
      omega
    have hd : (g₂ * vanishingPoly dom E₁
        - g₁ * vanishingPoly dom E₂).natDegree < w :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt e1 e2)
    omega
  have heq : g₂ * vanishingPoly dom E₁ = g₁ * vanishingPoly dom E₂ :=
    sub_eq_zero.mp hzero
  -- factor: m_{E₁} ∣ g₁, m_{E₂} ∣ g₂ (disjoint extras)
  obtain ⟨c₁, hc₁⟩ : vanishingPoly dom E₁ ∣ g₁ := by
    have h1 : vanishingPoly dom E₁ ∣ g₁ * vanishingPoly dom E₂ :=
      ⟨g₂, by linear_combination -heq⟩
    exact (isCoprime_vanishingPoly_disjoint dom hdisjE).dvd_of_dvd_mul_right h1
  obtain ⟨c₂, hc₂⟩ : vanishingPoly dom E₂ ∣ g₂ := by
    have h1 : vanishingPoly dom E₂ ∣ g₂ * vanishingPoly dom E₁ :=
      ⟨g₁, by linear_combination heq⟩
    exact (isCoprime_vanishingPoly_disjoint dom hdisjE.symm).dvd_of_dvd_mul_right h1
  have hc₁ne : c₁ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc₁
    exact hg₁ hc₁
  have hc₂ne : c₂ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc₂
    exact hg₂ hc₂
  -- the telescoped identities: Φᵢ·m_K = cᵢ·m_D
  have htel₁ : (R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁))
      * vanishingPoly dom K = c₁ * vanishingPoly dom Finset.univ := by
    refine mul_right_cancel₀ (vanishingPoly_ne_zero dom E₁) ?_
    calc (R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁))
        * vanishingPoly dom K * vanishingPoly dom E₁
        = (R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁))
          * (vanishingPoly dom K * vanishingPoly dom E₁) := by ring
      _ = (g₁ * vanishingPoly dom S₁) * vanishingPoly dom S₁ᶜ := by
          rw [← hm₁, hid₁]
      _ = g₁ * (vanishingPoly dom S₁ * vanishingPoly dom S₁ᶜ) := by ring
      _ = g₁ * vanishingPoly dom Finset.univ := by
          rw [vanishingPoly_mul_compl dom S₁]
      _ = (vanishingPoly dom E₁ * c₁) * vanishingPoly dom Finset.univ := by
          rw [← hc₁]
      _ = c₁ * vanishingPoly dom Finset.univ * vanishingPoly dom E₁ := by ring
  have htel₂ : (R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁))
      * vanishingPoly dom K = c₂ * vanishingPoly dom Finset.univ := by
    refine mul_right_cancel₀ (vanishingPoly_ne_zero dom E₂) ?_
    calc (R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁))
        * vanishingPoly dom K * vanishingPoly dom E₂
        = (R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁))
          * (vanishingPoly dom K * vanishingPoly dom E₂) := by ring
      _ = (g₂ * vanishingPoly dom S₂) * vanishingPoly dom S₂ᶜ := by
          rw [← hm₂, hid₂]
      _ = g₂ * (vanishingPoly dom S₂ * vanishingPoly dom S₂ᶜ) := by ring
      _ = g₂ * vanishingPoly dom Finset.univ := by
          rw [vanishingPoly_mul_compl dom S₂]
      _ = (vanishingPoly dom E₂ * c₂) * vanishingPoly dom Finset.univ := by
          rw [← hc₂]
      _ = c₂ * vanishingPoly dom Finset.univ * vanishingPoly dom E₂ := by ring
  -- subtraction pins c₁ = c₂
  have hsub : (ℓ₀ * ((C γ₁ - C γ₂) * R₁ - (C p₁ - C p₂) * ℓ₁))
      * vanishingPoly dom K = (c₁ - c₂) * vanishingPoly dom Finset.univ := by
    linear_combination htel₁ - htel₂
  have hcdeg₁ : c₁.natDegree < w := by
    have hmul := Polynomial.natDegree_mul (vanishingPoly_ne_zero dom E₁) hc₁ne
    rw [← hc₁, vanishingPoly_natDegree] at hmul
    omega
  have hcdeg₂ : c₂.natDegree < w := by
    have hmul := Polynomial.natDegree_mul (vanishingPoly_ne_zero dom E₂) hc₂ne
    rw [← hc₂, vanishingPoly_natDegree] at hmul
    omega
  have hceq : c₁ = c₂ := by
    by_contra hne
    have hCne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
    have hdvdc : ℓ₀ ∣ (c₁ - c₂) * vanishingPoly dom Finset.univ :=
      ⟨((C γ₁ - C γ₂) * R₁ - (C p₁ - C p₂) * ℓ₁) * vanishingPoly dom K,
        by linear_combination -hsub⟩
    have hdvdc' : ℓ₀ ∣ c₁ - c₂ :=
      (isCoprime_vanishingPoly dom hG₀ _).dvd_of_dvd_mul_right hdvdc
    have hdeg := Polynomial.natDegree_le_of_dvd hdvdc' hCne
    have hlt : (c₁ - c₂).natDegree < w :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hcdeg₁ hcdeg₂)
    omega
  -- Φ₁ = Φ₂, then second-row reducedness
  rw [hceq, sub_self, zero_mul] at hsub
  have h1 : ℓ₀ * ((C γ₁ - C γ₂) * R₁ - (C p₁ - C p₂) * ℓ₁) = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact h
    · exact absurd h (vanishingPoly_ne_zero dom K)
  have h2 : (C γ₁ - C γ₂) * R₁ - (C p₁ - C p₂) * ℓ₁ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hℓ₀ne
    · exact h
  have hcancel : (C γ₁ - C γ₂) * R₁ = (C p₁ - C p₂) * ℓ₁ := by
    linear_combination h2
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

end Telescope

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.vanishingPoly_union_disjoint
#print axioms ProximityGap.WBPencil.isCoprime_vanishingPoly_disjoint
#print axioms ProximityGap.WBPencil.window_pair_telescope
