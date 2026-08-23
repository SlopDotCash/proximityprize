/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MonomialDominationPin
import ArkLib.Data.CodingTheory.ProximityGap.SmoothWindowSaturation
import ArkLib.Data.CodingTheory.ProximityGap.UniversalSpikeFloor

/-!
# Red team round 3: `MonomialDomination` REFUTED on the low bands — and the hybrid repair

The third self-applied kill in the extremality-surface lineage (after the
agreement-matched census and its floor repair). The fleet's **universal spike floor**
(`epsMCA_ge_j_div_card`) realizes `j` bad scalars on band `j` with per-position
coefficient freedom (`u₀ = Σ aₗ·e_{pₗ}`, `u₁ = Σ e_{pₗ}`, distinct `aₗ`) — freedom
**monomial pairs do not have**. At the `(F₁₇, μ₈, k = 2)` instance, band 2
(agreement `a = 7`, `δ·n = 1`):

* `epsMCA_band2_ge` — the spike floor gives `ε_mca ≥ 2/17` (the no-weight-`≤ 2`
  hypothesis is the affine two-roots argument);
* `monomial_band2_le` — **every monomial pair has at most one bad scalar at
  agreement 7, by structure** (no enumeration): two bad scalars subtract to
  `(λ − λ′)·x^t = affine` on `≥ 6` of the 8 points; for `2 ≤ t ≤ 3` the direct degree
  count kills it, for `4 ≤ t ≤ 7` the reciprocal trick (`x⁸ = 1` on `μ₈`) transports it
  to a degree-`≤ 5` polynomial with `≥ 6` roots, and for `t ≤ 1` the second row is
  itself a codeword, so the event never fires at all;
* `monomialDomination_killed` — hence `monomialEps ≤ 1/17 < 2/17 ≤ ε_mca` at `a = 7`:
  **`MonomialDomination dom8 C ac` is false for every `ac < 7`** — every window
  crossing's quantifier range hits band 2 and dies there.

**The repair (v4): hybrid domination.** The corrected surface takes the maximum of the
monomial error and the staircase term `(n − a + 1)/|F|` — the latter is an exact
*theorem* on every band below a third of the distance (the band collapse / exact
staircase), so the conjectural content of `HybridDomination` is confined to the
structured-and-window regime, exactly where the probes support it. The v4 pin
(`mcaDeltaStar_eq_of_hybridCrossing`) runs the same engine with the max in the
numerics. This is the formal twin of the empirical O146/O152 correction (the
two-family max law: 9 instances, 14+ field-combos, zero deviations).

The surface lineage, honestly: census (killed at empty rungs) → census+floor (killed
by the take-over) → monomial (killed on low bands, this file) → **hybrid
(monomial ∪ spike): consistent with every theorem and every probe now in the tree.**

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357; `UniversalSpikeFloor.lean` (the killer), `MonomialDominationPin.lean`
  (the victim), `SmoothWindowSaturation.lean` (the instance API).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MonomialDominationKilled

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial Finset
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothWindowSaturation
open ProximityGap.MonomialDominationPin
open ProximityGap.SpikeFloor

/-! ## The spike side: `ε_mca ≥ 2/17` on band 2 -/

/-- The degree-`< 2` code on `μ₈` has no nonzero codeword of weight `≤ 2`: an affine
function vanishing on six of the eight (distinct) points has two distinct roots. -/
theorem noWeightLE_two : NoWeightLE (evalCode dom8 2) 2 := by
  rintro w hw ⟨T, hTcard, hTzero⟩
  obtain ⟨q, hq, hw_eq⟩ := (mem_evalCode w).mp hw
  obtain ⟨c₁, c₀, hq_aff⟩ := exists_eq_X_add_C_of_natDegree_le_one hq
  have hcompl : 6 ≤ (Finset.univ \ T).card := by
    have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
    have hu : (Finset.univ : Finset (Fin 8)).card = 8 := by decide
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (Finset.univ \ T).card)
  have hzi : w i = 0 := hTzero i (Finset.mem_sdiff.mp hi).2
  have hzj : w j = 0 := hTzero j (Finset.mem_sdiff.mp hj).2
  have heval : ∀ l : Fin 8, w l = c₁ * dom8 l + c₀ := by
    intro l
    rw [hw_eq l, hq_aff]
    simp [eval_add, eval_mul, eval_C, eval_X]
  have hvi : c₁ * dom8 i + c₀ = 0 := by rw [← heval i]; exact hzi
  have hvj : c₁ * dom8 j + c₀ = 0 := by rw [← heval j]; exact hzj
  have hdne : dom8 i ≠ dom8 j := fun h => hij (dom8_injective h)
  have hc1 : c₁ = 0 := by
    by_contra hc1ne
    refine hdne ?_
    have hsub : c₁ * dom8 i = c₁ * dom8 j := by
      have := hvi.trans hvj.symm
      exact add_right_cancel this
    exact mul_left_cancel₀ hc1ne hsub
  have hc0 : c₀ = 0 := by
    rw [hc1, zero_mul, zero_add] at hvi
    exact hvi
  funext l
  simp [heval l, hc1, hc0]

/-- **Band-2 spike floor at the instance:** `ε_mca(C, 1 − 7/8) ≥ 2/17`. -/
theorem epsMCA_band2_ge :
    (2 : ℝ≥0∞) / 17
      ≤ epsMCA (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
          (1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) := by
  have h := epsMCA_ge_j_div_card (j := 2) (evalCode dom8 2) noWeightLE_two
    (δ := 1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) ?_ (by norm_num)
    (by rw [Fintype.card_fin]; norm_num)
    ⟨![0, 1], by decide⟩ ⟨![0, 1], by decide⟩ (b := (1 : F17)) one_ne_zero
  · have hF : (Fintype.card F17 : ℝ≥0∞) = 17 := by rw [ZMod.card]; norm_num
    rw [hF] at h
    exact_mod_cast h
  · rw [Fintype.card_fin]
    have hval : (1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) * ((8 : ℕ) : ℝ≥0) = 1 := by
      rw [tsub_mul, div_mul_cancel₀ _ (by norm_num : ((8 : ℕ) : ℝ≥0) ≠ 0), one_mul]
      apply NNReal.coe_injective
      rw [NNReal.coe_sub (by exact_mod_cast (by norm_num : (7 : ℕ) ≤ 8))]
      push_cast
      norm_num
    rw [hval]
    norm_num

/-! ## The monomial side: structural `≤ 1` at agreement 7 -/

/-- The domain consists of eighth roots of unity. -/
theorem dom8_pow_eight : ∀ l : Fin 8, dom8 l ^ 8 = 1 := by decide

/-- Unpack the MCA event at a grid agreement into a witness with an affine
explanation of the line and the no-joint clause. -/
theorem event_data {u v : Fin 8 → F17} {a : ℕ} (ha2 : 2 ≤ a) (han : a ≤ 8)
    {lam : F17}
    (h : mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((a : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) u v lam) :
    ∃ T : Finset (Fin 8), a ≤ T.card ∧
      (∃ c₁ c₀ : F17, ∀ l ∈ T, u l + lam * v l = c₁ * dom8 l + c₀) ∧
      ¬ pairJointAgreesOn (evalCode dom8 2 : Set (Fin 8 → F17)) T u v := by
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; omega)] at h
  obtain ⟨T, hcard, ⟨w, hw, hag⟩, hno⟩ := h
  obtain ⟨q, hq, hw_eq⟩ := (mem_evalCode w).mp hw
  obtain ⟨c₁, c₀, hq_aff⟩ := exists_eq_X_add_C_of_natDegree_le_one hq
  refine ⟨T, hcard, ⟨c₁, c₀, fun l hl => ?_⟩, hno⟩
  have h1 : w l = u l + lam * v l := by
    rw [hag l hl, smul_eq_mul]
  have h2 : w l = c₁ * dom8 l + c₀ := by
    rw [hw_eq l, hq_aff]
    simp [eval_add, eval_mul, eval_C, eval_X]
  rw [← h1, h2]

/-- A nonzero polynomial of degree `< 6` cannot vanish on six points of the domain. -/
theorem no_six_roots {G : Polynomial F17} (hG : G ≠ 0) (hdeg : G.natDegree < 6)
    {S : Finset (Fin 8)} (hS : 6 ≤ S.card)
    (hvan : ∀ l ∈ S, G.eval (dom8 l) = 0) : False := by
  classical
  have hsub : S.image dom8 ⊆ G.roots.toFinset := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hG]
    exact hvan l hl
  have hcount : 6 ≤ G.natDegree := by
    calc 6 ≤ S.card := hS
      _ = (S.image dom8).card := (Finset.card_image_of_injective S dom8_injective).symm
      _ ≤ G.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card G.roots := Multiset.toFinset_card_le _
      _ ≤ G.natDegree := Polynomial.card_roots' G
  omega

/-- **The codeword-row case (`t ≤ 1`): the event never fires.** If the second row is
itself affine, any affine explanation of the line yields a joint explanation. -/
theorem no_event_of_low_t {s : Fin 8} {t : Fin 8} (ht : (t : ℕ) ≤ 1) (lam : F17) :
    ¬ mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0))
      (fun i => dom8 i ^ (s : ℕ)) (fun i => dom8 i ^ (t : ℕ)) lam := by
  intro h
  obtain ⟨T, hcard, ⟨c₁, c₀, hline⟩, hno⟩ := event_data (by norm_num) (by norm_num) h
  -- the second row is the affine `vc₁·x + vc₀`
  obtain ⟨vc₁, vc₀, hv⟩ : ∃ vc₁ vc₀ : F17,
      ∀ l : Fin 8, dom8 l ^ (t : ℕ) = vc₁ * dom8 l + vc₀ := by
    interval_cases ht' : (t : ℕ)
    · exact ⟨0, 1, fun l => by rw [pow_zero]; ring⟩
    · exact ⟨1, 0, fun l => by rw [pow_one]; ring⟩
  refine hno ⟨fun l => (c₁ - lam * vc₁) * dom8 l + (c₀ - lam * vc₀), ?_,
    fun l => vc₁ * dom8 l + vc₀, ?_, fun l hl => ⟨?_, ?_⟩⟩
  · exact affine_mem _ _
  · exact affine_mem _ _
  · -- row 0 agreement: u = line − λ·v
    show (c₁ - lam * vc₁) * dom8 l + (c₀ - lam * vc₀) = dom8 l ^ (s : ℕ)
    have h1 := hline l hl
    have h2 := hv l
    have hsplit : (c₁ - lam * vc₁) * dom8 l + (c₀ - lam * vc₀)
        = (c₁ * dom8 l + c₀) - lam * (vc₁ * dom8 l + vc₀) := by ring
    rw [hsplit, ← h1, ← h2]
    ring
  · show vc₁ * dom8 l + vc₀ = dom8 l ^ (t : ℕ)
    exact (hv l).symm

/-- **The high-`t` case: at most one bad scalar.** Two bad scalars subtract to an
affine identity for `(λ − λ′)·x^t` on `≥ 6` points; the direct degree count kills
`2 ≤ t ≤ 3`, the reciprocal `x⁸ = 1` transport kills `4 ≤ t ≤ 7`. -/
theorem at_most_one_of_high_t {s t : Fin 8} (ht : 2 ≤ (t : ℕ))
    {lam lam' : F17}
    (h : mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0))
      (fun i => dom8 i ^ (s : ℕ)) (fun i => dom8 i ^ (t : ℕ)) lam)
    (h' : mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0))
      (fun i => dom8 i ^ (s : ℕ)) (fun i => dom8 i ^ (t : ℕ)) lam') :
    lam = lam' := by
  classical
  by_contra hne
  obtain ⟨T, hTcard, ⟨c₁, c₀, hline⟩, -⟩ := event_data (by norm_num) (by norm_num) h
  obtain ⟨T', hTcard', ⟨d₁, d₀, hline'⟩, -⟩ := event_data (by norm_num) (by norm_num) h'
  -- the intersection has ≥ 6 points
  have hcap : 6 ≤ (T ∩ T').card := by
    have hunion : (T ∪ T').card ≤ 8 := by
      calc (T ∪ T').card ≤ (Finset.univ : Finset (Fin 8)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = 8 := by decide
    have hsum := Finset.card_union_add_card_inter T T'
    omega
  -- subtraction: (λ − λ′)·x^t = (c₁ − d₁)·x + (c₀ − d₀) on T ∩ T′
  have hμ : lam - lam' ≠ 0 := sub_ne_zero.mpr hne
  have hsub : ∀ l ∈ T ∩ T', (lam - lam') * dom8 l ^ (t : ℕ)
      = (c₁ - d₁) * dom8 l + (c₀ - d₀) := by
    intro l hl
    have h1 := hline l (Finset.mem_inter.mp hl).1
    have h2 := hline' l (Finset.mem_inter.mp hl).2
    have := congrArg₂ (· - ·) h1 h2
    simp only at this
    linear_combination this
  rcases Nat.lt_or_ge (t : ℕ) 4 with ht4 | ht4
  · -- 2 ≤ t ≤ 3: direct degree count
    set G : Polynomial F17 :=
      C (lam - lam') * X ^ (t : ℕ) - (C (c₁ - d₁) * X + C (c₀ - d₀)) with hG
    have hGne : G ≠ 0 := by
      intro h0
      have hcoeff : G.coeff (t : ℕ) = lam - lam' := by
        rw [hG]
        rw [coeff_sub, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one,
          coeff_add, coeff_C_mul, coeff_X, coeff_C]
        have h1 : ¬((t : ℕ) = 1) := by omega
        have h2 : ¬((t : ℕ) = 0) := by omega
        have h1' : ¬((1 : ℕ) = (t : ℕ)) := by omega
        have h2' : ¬((0 : ℕ) = (t : ℕ)) := by omega
        simp [h1, h2, h1', h2']
      rw [h0, Polynomial.coeff_zero] at hcoeff
      exact hμ hcoeff.symm
    have hGdeg : G.natDegree < 6 := by
      rw [hG]
      have hd1 : (C (lam - lam') * X ^ (t : ℕ)).natDegree ≤ (t : ℕ) := by
        refine le_trans natDegree_mul_le ?_
        rw [natDegree_C, natDegree_X_pow]
        omega
      have hd2 : (C (c₁ - d₁) * X + C (c₀ - d₀)).natDegree ≤ 1 := by
        refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
        · refine le_trans natDegree_mul_le ?_
          simp [natDegree_C, natDegree_X]
        · simp [natDegree_C]
      have := natDegree_sub_le (C (lam - lam') * X ^ (t : ℕ))
        (C (c₁ - d₁) * X + C (c₀ - d₀))
      have htle : (t : ℕ) ≤ 3 := by omega
      omega
    refine no_six_roots hGne hGdeg hcap fun l hl => ?_
    rw [hG]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    rw [sub_eq_zero]
    exact hsub l hl
  · -- 4 ≤ t ≤ 7: reciprocal transport via x⁸ = 1
    set G : Polynomial F17 :=
      C (c₁ - d₁) * X ^ (9 - (t : ℕ)) + C (c₀ - d₀) * X ^ (8 - (t : ℕ))
        - C (lam - lam') with hG
    have ht8 : (t : ℕ) ≤ 7 := by omega
    have hGne : G ≠ 0 := by
      intro h0
      have hcoeff : G.coeff 0 = -(lam - lam') := by
        rw [hG]
        rw [coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow,
          coeff_C]
        have h1 : ¬((0 : ℕ) = 9 - (t : ℕ)) := by omega
        have h2 : ¬((0 : ℕ) = 8 - (t : ℕ)) := by omega
        simp [h1, h2]
      rw [h0, Polynomial.coeff_zero] at hcoeff
      exact hμ (neg_eq_zero.mp hcoeff.symm)
    have hGdeg : G.natDegree < 6 := by
      rw [hG]
      have hd1 : (C (c₁ - d₁) * X ^ (9 - (t : ℕ))).natDegree ≤ 9 - (t : ℕ) := by
        refine le_trans natDegree_mul_le ?_
        rw [natDegree_C, natDegree_X_pow]
        omega
      have hd2 : (C (c₀ - d₀) * X ^ (8 - (t : ℕ))).natDegree ≤ 8 - (t : ℕ) := by
        refine le_trans natDegree_mul_le ?_
        rw [natDegree_C, natDegree_X_pow]
        omega
      have hadd := natDegree_add_le (C (c₁ - d₁) * X ^ (9 - (t : ℕ)))
        (C (c₀ - d₀) * X ^ (8 - (t : ℕ)))
      have hsub' := natDegree_sub_le
        (C (c₁ - d₁) * X ^ (9 - (t : ℕ)) + C (c₀ - d₀) * X ^ (8 - (t : ℕ)))
        (C (lam - lam') : Polynomial F17)
      have hC : (C (lam - lam') : Polynomial F17).natDegree = 0 := natDegree_C _
      omega
    refine no_six_roots hGne hGdeg hcap fun l hl => ?_
    rw [hG]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    rw [sub_eq_zero]
    -- multiply the subtraction identity by x^{8−t} and use x⁸ = 1
    have hkey := hsub l hl
    have hpow : dom8 l ^ (t : ℕ) * dom8 l ^ (8 - (t : ℕ)) = 1 := by
      rw [← pow_add]
      have : (t : ℕ) + (8 - (t : ℕ)) = 8 := by omega
      rw [this]
      exact dom8_pow_eight l
    have hmul := congrArg (· * dom8 l ^ (8 - (t : ℕ))) hkey
    simp only at hmul
    have hlhs : (lam - lam') * dom8 l ^ (t : ℕ) * dom8 l ^ (8 - (t : ℕ))
        = lam - lam' := by
      rw [mul_assoc, hpow, mul_one]
    have hx9 : dom8 l * dom8 l ^ (8 - (t : ℕ)) = dom8 l ^ (9 - (t : ℕ)) := by
      have : 9 - (t : ℕ) = (8 - (t : ℕ)) + 1 := by omega
      rw [this, pow_succ]
      ring
    calc (c₁ - d₁) * dom8 l ^ (9 - (t : ℕ)) + (c₀ - d₀) * dom8 l ^ (8 - (t : ℕ))
        = ((c₁ - d₁) * dom8 l + (c₀ - d₀)) * dom8 l ^ (8 - (t : ℕ)) := by
          rw [← hx9]; ring
      _ = (lam - lam') * dom8 l ^ (t : ℕ) * dom8 l ^ (8 - (t : ℕ)) := by
          rw [← hmul]
      _ = lam - lam' := hlhs

open Classical in
/-- **Every monomial pair has at most one bad scalar at agreement 7** — hence
`monomialEps ≤ 1/17` on band 2. Fully structural: no enumeration. -/
theorem monomial_band2_le :
    monomialEps dom8 (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) ≤ (1 : ℝ≥0∞) / 17 := by
  unfold monomialEps
  refine iSup_le fun s => iSup_le fun t => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  have hF : ((Fintype.card F17 : ℝ≥0) : ℝ≥0∞) = 17 := by
    rw [ZMod.card]; norm_cast
  rw [hF]
  have hgrid : (1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) : ℝ≥0)
      = 1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0) := by
    rw [Fintype.card_fin]
  have hcard : (Finset.univ.filter (fun lam : F17 =>
      mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
        (1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0))
        (fun i => dom8 i ^ (s : ℕ)) (fun i => dom8 i ^ (t : ℕ)) lam)).card ≤ 1 := by
    rcases Nat.lt_or_ge (t : ℕ) 2 with ht | ht
    · -- t ≤ 1: the filter is empty
      have hempty : Finset.univ.filter (fun lam : F17 =>
          mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
            (1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0))
            (fun i => dom8 i ^ (s : ℕ)) (fun i => dom8 i ^ (t : ℕ)) lam) = ∅ := by
        refine Finset.filter_false_of_mem fun lam _ => ?_
        intro hev
        rw [hgrid] at hev
        exact no_event_of_low_t (s := s) (by omega) lam hev
      rw [hempty]
      simp
    · -- t ≥ 2: at most one element
      rw [Finset.card_le_one]
      intro lam hlam lam' hlam'
      rw [Finset.mem_filter] at hlam hlam'
      have h1 := hlam.2
      have h2 := hlam'.2
      rw [hgrid] at h1 h2
      exact at_most_one_of_high_t ht h1 h2
  gcongr
  exact_mod_cast hcard

/-! ## The kill -/

/-- **`MonomialDomination` is FALSE** at `(F₁₇, μ₈, 2)` for every crossing `ac < 7`:
the spike pencil realizes `2/17` on band 2 where every monomial pair is capped at
`1/17`. Red-team kill 3 in the extremality-surface lineage. -/
theorem monomialDomination_killed (ac : ℕ) (hac : ac < 7) :
    ¬ MonomialDomination dom8 (evalCode dom8 2 : Set (Fin 8 → F17)) ac := by
  intro hdom
  have h := hdom 7 hac (by norm_num)
  have hchain : (2 : ℝ≥0∞) / 17 ≤ 1 / 17 :=
    le_trans epsMCA_band2_ge (le_trans h monomial_band2_le)
  have h12 : (1 : ℝ≥0∞) / 17 < 2 / 17 := by
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num),
      ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    norm_num
  exact absurd hchain (not_le.mpr h12)

/-! ## The repair: hybrid domination and the v4 pin -/

section Repair

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} (dom : Fin n → F)

/-- **The v4 named surface — hybrid domination:** above the crossing, the MCA error is
dominated by the *maximum* of the monomial error and the staircase term
`(n − a + 1)/|F|`. The staircase term is an exact theorem on every band below a third
of the distance; the conjectural content is confined to the structured/window regime.
Consistent with every theorem and probe in the tree (spike pencils included). -/
def HybridDomination (C : Set (Fin n → F)) (ac : ℕ) : Prop :=
  ∀ a : ℕ, ac < a → a ≤ n →
    epsMCA (F := F) (A := F) C (1 - (a : ℝ≥0) / (n : ℝ≥0))
      ≤ max (monomialEps dom C (1 - (a : ℝ≥0) / (n : ℝ≥0)))
          (((n - a + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))

open Classical in
/-- **The hybrid-domination δ\* pin (v4).** Hybrid domination above the crossing +
hybrid numerics (both terms clear `ε*` above the crossing) + any bad witness at the
crossing pin `mcaDeltaStar = 1 − ac/n` exactly. -/
theorem mcaDeltaStar_eq_of_hybridCrossing [Nonempty (Fin n)]
    (C : Set (Fin n → F)) (εstar : ℝ≥0∞) {ac : ℕ}
    (hdom : HybridDomination dom C ac)
    (hnum : ∀ a : ℕ, ac < a → a ≤ n →
      max (monomialEps dom C (1 - (a : ℝ≥0) / (n : ℝ≥0)))
          (((n - a + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤ εstar)
    (hbad : εstar < epsMCA (F := F) (A := F) C (1 - (ac : ℝ≥0) / (n : ℝ≥0))) :
    mcaDeltaStar (F := F) (A := F) C εstar = 1 - (ac : ℝ≥0) / (n : ℝ≥0) := by
  refine MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump C εstar tsub_le_self ?_
    hbad
  intro δ hδ
  have hquant := epsMCA_eq_grid (F := F) (A := F) C δ
  rw [Fintype.card_fin] at hquant
  rw [hquant]
  set a := agreeOf n δ with ha
  have hale : a ≤ n := by
    rw [ha]
    exact agreeOf_le n δ
  have hac_lt : ac < a := by
    have h2 : (ac : ℝ≥0) / (n : ℝ≥0) < 1 - δ := by
      rw [lt_tsub_iff_right]
      calc (ac : ℝ≥0) / (n : ℝ≥0) + δ = δ + (ac : ℝ≥0) / (n : ℝ≥0) := add_comm _ _
        _ < 1 := by rwa [← lt_tsub_iff_right]
    have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by
      have : 0 < n := Fin.pos_iff_nonempty.mpr ‹Nonempty (Fin n)›
      exact_mod_cast this
    have h3 : (ac : ℝ≥0) < (1 - δ) * (n : ℝ≥0) := by
      have := mul_lt_mul_of_pos_right h2 hn0
      rwa [div_mul_cancel₀ _ (ne_of_gt hn0)] at this
    rw [ha]
    unfold agreeOf
    exact Nat.lt_ceil.mpr h3
  exact le_trans (hdom a hac_lt hale) (hnum a hac_lt hale)

end Repair

/-! ## Source audit -/

#print axioms noWeightLE_two
#print axioms epsMCA_band2_ge
#print axioms no_event_of_low_t
#print axioms at_most_one_of_high_t
#print axioms monomial_band2_le
#print axioms monomialDomination_killed
#print axioms mcaDeltaStar_eq_of_hybridCrossing

end ProximityGap.MonomialDominationKilled
