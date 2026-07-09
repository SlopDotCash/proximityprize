/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralKMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.SparseDirectionGeneralK
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The universal below-UDR law, all rates (#371): the assembly

The general-rate analogue of the `k = 1` universal law: for **every** stack and
every radius `δ ≤ w/n` with `2w + 2k ≤ n`,

  **`#bad · (n − 2w − 2k + 1)^k ≤ n^{k+1}`**.

The dichotomy on the direction's maximum codeword agreement `a*`:

* `a* ≤ n − w − k − 1`: the general-`k` multiplicity theorem applies, and its
  factor dominates `(n−2w−2k+1)^k` (descending factorial ≥ the power);
* `a* ≥ n − w − k`: the direction is within `w + k` of a codeword; translation
  equivariance reduces to a sparse direction with support `≤ w + k`, and the
  general-`k` sparse bound's factor is exactly `(n−2w−2k+1)^k`.

No class hypotheses.  Mass `≤ n^{k+1}/((n−2w−2k+1)^k·q)` — polynomial in `n` at
every fixed rate, production-silent throughout the covered range, which reaches
within `k/n` of the unique-decoding radius.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE UNIVERSAL BELOW-UDR LAW, ALL RATES**: every stack, every radius
`δ ≤ w/n` with `2w + 2k ≤ n`:  `#bad · (n−2w−2k+1)^k ≤ n^{k+1}`. -/
theorem generalK_badScalars_card_mul_le_universal (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + 2 * k ≤ n)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * (n - 2 * w - 2 * k + 1) ^ k ≤ n ^ (k + 1) := by
  by_cases hcase : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ n - w - k - 1
  · -- multiplicity regime
    have hmult := badScalars_card_mul_le_of_agreement dom hk hδn
      (u₀ := u₀) (u₁ := u₁) hcase
    have hcardfun : Fintype.card (Fin (k + 1) → Fin n) = n ^ (k + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [hcardfun] at hmult
    refine le_trans (Nat.mul_le_mul_left _ ?_) hmult
    -- (n−2w−2k+1)^k ≤ descFactorial · (n−w−k−μ) with μ = n−w−k−1
    have hfac : n - w - k - (n - w - k - 1) = 1 ∨ n - w - k = 0 := by omega
    have h1 : 1 ≤ n - w - k - (n - w - k - 1) := by omega
    calc (n - 2 * w - 2 * k + 1) ^ k
        ≤ ((n - w) + 1 - k) ^ k := by
          refine Nat.pow_le_pow_left ?_ k
          omega
      _ ≤ (n - w).descFactorial k := Nat.pow_sub_le_descFactorial _ _
      _ = (n - w).descFactorial k * 1 := (mul_one _).symm
      _ ≤ (n - w).descFactorial k * (n - w - k - (n - w - k - 1)) :=
          Nat.mul_le_mul_left _ h1
  · -- near-codeword regime: translate and use the general-k sparse bound
    push Not at hcase
    obtain ⟨c, hcC, hagree⟩ := hcase
    have haN : n - w - k ≤ (agreeSet c u₁).card := by omega
    set ε : Fin n → F := u₁ - c with hε
    -- support of ε = complement of the agreement set
    have hsupp : (Finset.univ.filter (fun i => ε i ≠ 0)).card ≤ w + k := by
      have hcompl : Finset.univ.filter (fun i => ε i ≠ 0)
          = Finset.univ.filter (fun i => ¬ c i = u₁ i) := by
        refine Finset.filter_congr fun i _ => ?_
        rw [hε]
        simp [sub_eq_zero, eq_comm]
      rw [hcompl]
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => c i = u₁ i)
      have huniv : (Finset.univ : Finset (Fin n)).card = n := by
        rw [Finset.card_univ, Fintype.card_fin]
      have hagreecard : (agreeSet c u₁).card
          = (Finset.univ.filter (fun i => c i = u₁ i)).card := rfl
      omega
    -- translation: the bad sets agree
    have hfilter : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
        = (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)) := by
      refine Finset.filter_congr fun γ _ => ?_
      have h := ProximityGap.MCAEquivariance.mcaEvent_translate
        (rsCode dom k : Submodule F (Fin n → F)) (δ := δ)
        (u₀ := u₀) (u₁ := ε)
        (c₀ := 0) (c₁ := c)
        ((rsCode dom k : Submodule F (Fin n → F)).zero_mem) hcC γ
      have he0 : u₀ + 0 = u₀ := by funext i; simp
      have he1 : ε + c = u₁ := by
        funext i
        rw [hε]
        simp
      rw [he0, he1] at h
      rw [h]
    rw [hfilter]
    have hmk' : k ≤ n - w - (w + k) := by omega
    have hsparse := sparse_direction_badScalars_card_le_generalK dom
      (w := w) (e := w + k) hδn hmk' (u₀ := u₀) (ε := ε) hsupp
    have hfaceq : (n - w - (w + k)) + 1 - k = n - 2 * w - 2 * k + 1 := by omega
    rw [hfaceq] at hsparse
    calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
          * (n - 2 * w - 2 * k + 1) ^ k
        ≤ n ^ k * (w + k) := hsparse
      _ ≤ n ^ k * n := Nat.mul_le_mul_left _ (by omega)
      _ = n ^ (k + 1) := by rw [pow_succ]

open Classical in
/-- **The probability form**: `ε_mca(RS_k, δ) ≤ n^{k+1}/((n−2w−2k+1)^k·q)` for
every `δ ≤ w/n` with `2w + 2k ≤ n` — the universal below-UDR law at all rates. -/
theorem generalK_epsMCA_le_universal (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + 2 * k ≤ n)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n ^ (k + 1) / (n - 2 * w - 2 * k + 1) ^ k : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  have h := generalK_badScalars_card_mul_le_universal dom hk hn hδn (u 0) (u 1)
  have hpos : 0 < (n - 2 * w - 2 * k + 1) ^ k := by positivity
  have hdiv : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ (u 0) (u 1)
      γ)).card ≤ n ^ (k + 1) / (n - 2 * w - 2 * k + 1) ^ k :=
    Nat.le_div_iff_mul_le hpos |>.mpr h
  exact_mod_cast hdiv

open Classical in
/-- **The unconditional production floor**: `δ* ≥ δ` for every radius `δ ≤ w/n`
with `2w + 2k ≤ n`, whenever the polynomial mass fits the budget — for low rates
this floor `≈ 1/2 − ρ` strictly improves the ladder reach `(1−ρ)/3`, with NO
named residual. -/
theorem le_mcaDeltaStar_universal (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + 2 * k ≤ n)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1) (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {εstar : ℝ≥0∞}
    (hbudget : ((n ^ (k + 1) / (n - 2 * w - 2 * k + 1) ^ k : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (generalK_epsMCA_le_universal dom hk hn hδn) hbudget)

open Classical in
/-- **THE ABOVE-UDR LOCALIZATION** — the multiplicity theorem is radius-free, so it
bites at EVERY radius, beyond UDR and through the window toward capacity: any
direction whose bad count exceeds the polynomial budget must be within `w + k` of
the code.  The above-UDR adversary provably lives in near-code directions —
the unconditional class-localization complementing the dimension ladder's exact
pins. -/
theorem above_udr_near_code_of_large_badCount (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F}
    (hbig : Fintype.card (Fin (k + 1) → Fin n)
      < (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        * ((n - w).descFactorial k)) :
    ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      n - w - k ≤ (agreeSet c u₁).card := by
  by_cases hz : n - w - k = 0
  · exact ⟨0, (rsCode dom k : Submodule F (Fin n → F)).zero_mem, by omega⟩
  by_contra hno
  push Not at hno
  have hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ n - w - k - 1 := by
    intro c hc
    have := hno c hc
    omega
  have hmult := badScalars_card_mul_le_of_agreement dom hk hδn
    (u₀ := u₀) (u₁ := u₁) hμ
  have h1 : 1 ≤ n - w - k - (n - w - k - 1) := by omega
  · have hge : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        * ((n - w).descFactorial k)
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        * ((n - w).descFactorial k * (n - w - k - (n - w - k - 1))) := by
      rw [← mul_assoc]
      refine Nat.le_mul_of_pos_right _ ?_
      omega
    exact absurd (le_trans hge hmult) (not_le.mpr hbig)

open Classical in
/-- **THE STRONGLY-FAR LAW** — radius-free, reaching capacity: a direction agreeing
with no codeword on more than `k` points has `#bad · (k+1)! ≤ n^{k+1}` at EVERY
radius `δ ≤ w/n` with `k + 1 ≤ n − w` (witnesses exist).  Probe-tight at the
boundary slice: far directions attain `C(n, k+1)` exactly — each `(k+1)`-subset of
a witness determines its scalar, disjointly. -/
theorem strongly_far_badScalars_card_mul_le (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * ((n - w).descFactorial (k + 1))
      ≤ Fintype.card (Fin (k + 1) → Fin n) := by
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) with hbad
  have hch : ∀ γ ∈ bad, ∃ S : Finset (Fin n),
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
      ∀ t : Fin (k + 1) → Fin n, (∀ a, t a ∈ S) →
        residual dom k t u₁ ≠ 0 →
        residual dom k t u₀ + γ * residual dom k t u₁ = 0 := by
    intro γ hγ
    exact mcaEvent_owned_tuples dom hk δ (Finset.mem_filter.mp hγ).2
  choose! W hWsz hWprop using hch
  set 𝒯 : F → Finset (Fin (k + 1) → Fin n) := fun γ =>
    Finset.univ.filter (fun t => (Function.Injective t ∧ ∀ a, t a ∈ W γ) ∧
      residual dom k t u₁ ≠ 0) with h𝒯
  refine badScalars_card_mul_le_ownership dom k u₀ u₁ bad _ 𝒯 ?_ ?_
  · intro γ hγ t ht
    obtain ⟨⟨-, htW⟩, hres⟩ := (Finset.mem_filter.mp ht).2
    exact ⟨hres, hWprop γ hγ t htW hres⟩
  · intro γ hγ
    -- EVERY injective tuple in the witness has nonzero residual (strong farness)
    have hSsz : n - w ≤ (W γ).card := by
      have h1 := hWsz γ hγ
      have h2 : ((n - w : ℕ) : ℝ≥0) ≤ ((W γ).card : ℝ≥0) := by
        have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
          rw [Fintype.card_fin]
        calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by rw [Nat.cast_tsub]
          _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
              exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
          _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
              rw [tsub_mul, one_mul, hcardn]
          _ ≤ ((W γ).card : ℝ≥0) := h1
      exact_mod_cast h2
    have hallres : ∀ t : Fin (k+1) → Fin n, Function.Injective t →
        residual dom k t u₁ ≠ 0 := by
      intro t htinj hres
      obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
      -- the tuple's k+1 points all lie in the agreement set: contradiction with ≤ k
      have hsub : Finset.univ.image t ⊆ agreeSet c u₁ := by
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hcag a⟩
      have hcard : k + 1 ≤ (agreeSet c u₁).card := by
        calc k + 1 = (Finset.univ.image t).card := by
              rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
                Fintype.card_fin]
          _ ≤ _ := Finset.card_le_card hsub
      have := hμ c hcC
      omega
    -- ownership: ALL injective tuples in the witness
    have hsub2 : Finset.univ.filter (fun t : Fin (k+1) → Fin n =>
        Function.Injective t ∧ ∀ a, t a ∈ W γ) ⊆ 𝒯 γ := by
      intro t ht
      obtain ⟨-, htinj, htmem⟩ := Finset.mem_filter.mp ht
      rw [h𝒯, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨htinj, htmem⟩, hallres t htinj⟩
    calc (n - w).descFactorial (k + 1)
        ≤ (W γ).card.descFactorial (k + 1) := Nat.descFactorial_le _ hSsz
      _ ≤ (Finset.univ.filter (fun t : Fin (k+1) → Fin n =>
            Function.Injective t ∧ ∀ a, t a ∈ W γ)).card :=
          injective_tuples_card_ge_descFactorial (W γ)
      _ ≤ (𝒯 γ).card := Finset.card_le_card hsub2

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.generalK_badScalars_card_mul_le_universal
#print axioms ProximityGap.Ownership.generalK_epsMCA_le_universal
#print axioms ProximityGap.Ownership.le_mcaDeltaStar_universal
#print axioms ProximityGap.Ownership.above_udr_near_code_of_large_badCount
#print axioms ProximityGap.Ownership.strongly_far_badScalars_card_mul_le
