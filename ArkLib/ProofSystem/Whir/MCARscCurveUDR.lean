/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CurveUDRBound
import ArkLib.ProofSystem.Whir.MCACurveSeam

/-!
# Cor 4.11 at every arity — the curve-UDR capstone (issues #302/#301/#304)

The final composition of the curve unique-decoding arc (stages 1–3:
`CurveUDRCoefficients`, `CurveUDRBadCount`, `CurveUDRBound`):

* `epsMCACurve_rs_full_le` — the full-agreement edge: at radii with `⌈(1−δ)n⌉ = n`, the curve
  MCA error is at most `(L−1)/|F|` (stage-1 interpolation makes the data stack itself a joint
  witness when `L` scalars agree everywhere).
* `mca_rsc_curve_udr` — **WHIR Corollary 4.11, unique-decoding branch, at EVERY arity**: the
  power generator for the smooth Reed–Solomon code has mutual correlated agreement with error
  `(L−1)·n/|F|` at the curve unique-decoding radius `δ < (n−2^m)/((L+1)·n)`. Generalizes the
  pair case (`mca_rsc_pair_holds`, `L = 2`) to all folding arities.

The radius is honestly `(1−ρ)/(L+1)`-shaped: the `L`-fold unique-decoding collapse genuinely
requires it. Mutual correlated agreement at the full pair radius `(1−ρ)/2` for `L > 2` (WHIR
Lemma 4.10's regime), and at the Johnson radius (WHIR Conjecture 4.12), remain open — see the
issue-#302 frontier map. Axiom-clean.
-/

open Finset ProximityGap ProximityGap.UDRwire ReedSolomon
open scoped NNReal ENNReal ProbabilityTheory

namespace MutualCorrAgreement

open ArkLib.ProximityGap.CurveUDR

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open Classical in
/-- Full-agreement wrapper: at radii so small that the witness threshold is everything
(`⌈(1−δ)n⌉ = n`), the curve MCA error is at most `(L−1)/|F|`. -/
theorem epsMCACurve_rs_full_le (α : ι ↪ F) (k : ℕ) (L : ℕ) (hL : 2 ≤ L) (δ : ℝ≥0)
    (htn : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = Fintype.card ι) :
    epsMCACurve (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) L δ
      ≤ ((L - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCACurve_le_of_badCount_le _ L δ _ (fun u => ?_)
  set G : Finset F := Finset.univ.filter
    (fun γ : F => mcaEventCurve (ReedSolomon.code α k : Set (ι → F)) δ u γ) with hGdef
  set Sf : F → Finset ι := fun γ =>
    if h : mcaEventCurve (ReedSolomon.code α k : Set (ι → F)) δ u γ
      then h.choose else ∅ with hSdef
  set wf : F → ι → F := fun γ =>
    if h : mcaEventCurve (ReedSolomon.code α k : Set (ι → F)) δ u γ
      then (h.choose_spec.2.1).choose else 0 with hwdef
  refine curveBadCount_full_le (ReedSolomon.code α k) L hL u G Sf wf ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    -- the witness set has at least `⌈(1−δ)n⌉ = n` elements, hence is everything
    have hcard : Fintype.card ι ≤ h.choose.card := by
      calc Fintype.card ι = ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ := htn.symm
        _ ≤ h.choose.card := Nat.ceil_le.mpr (by exact_mod_cast h.choose_spec.1)
    exact Finset.eq_univ_of_card _ (le_antisymm
      (by simpa using Finset.card_le_univ h.choose) hcard)
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    exact (h.choose_spec.2.1).choose_spec.1
  · intro γ hγ i hi
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    simp only [hSdef, dif_pos h] at hi
    have := (h.choose_spec.2.1).choose_spec.2 i hi
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => by rw [smul_eq_mul])
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    exact h.choose_spec.2.2


open Classical RSGenerator in
/-- **WHIR Corollary 4.11, unique-decoding branch, at EVERY arity** (curve-UD radius).
The power generator `Gen(L, α) = (1, α, …, α^{L−1})` for the smooth Reed–Solomon code has
mutual correlated agreement with error `(L−1)·n/|F|` (the `genRSC` unique-decoding error
shape) at the curve unique-decoding radius `δ < (n − 2^m)/((L+1)·n)`. Composes the stage-3
count bound (`epsMCACurve_rs_udr_le`) and the full-agreement edge (`epsMCACurve_rs_full_le`)
through the proven seam `hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`; generalizes the
landed pair case (`mca_rsc_pair_holds`) from `L = 2` to all arities. -/
theorem mca_rsc_curve_udr
    (φ : ι ↪ F) (m : ℕ) [Smooth φ] (L : ℕ) (hL : 2 ≤ L) (exp : Fin L ↪ ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι) (hexp : ∀ j : Fin L, exp j = (j : ℕ)) :
    haveI : Fintype (RSGenerator.genRSC (Fin L) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin L) φ m exp).hℓ
    hasMutualCorrAgreement (RSGenerator.genRSC (Fin L) φ m exp)
      (1 - ((Fintype.card ι - 2 ^ m : ℕ) : ℝ)
        / (((L : ℝ) + 1) * (Fintype.card ι : ℝ)))
      (fun _δ => (((L - 1) * Fintype.card ι : ℕ) : ℝ≥0∞)
        / ((Fintype.card F : ℕ) : ℝ≥0∞)) := by
  classical
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  set n := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hLR : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hB : (0 : ℝ) ≤ 1 - ((n - 2 ^ m : ℕ) : ℝ) / (((L : ℝ) + 1) * (n : ℝ)) := by
    have hle : ((n - 2 ^ m : ℕ) : ℝ) ≤ ((L : ℝ) + 1) * (n : ℝ) := by
      have h1 : ((n - 2 ^ m : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (Nat.sub_le _ _)
      nlinarith [h1, hnR, hLR]
    have := div_le_one_of_le₀ hle (by positivity)
    linarith
  refine hasMutualCorrAgreement_genRSC_of_epsMCACurve_le (by omega : 1 < L)
    φ m exp hexp _ hB _ (fun δ hδ0 hδB => ?_)
  rw [show ((RSGenerator.genRSC (Fin L) φ m exp).C : Set (ι → F))
      = (ReedSolomon.code φ (2 ^ m) : Set (ι → F)) from rfl]
  -- the radius gives the regime
  have hδB' : (δ : ℝ) * (((L : ℝ) + 1) * (n : ℝ)) < ((n - 2 ^ m : ℕ) : ℝ) := by
    have h := hδB
    rw [sub_sub_cancel] at h
    calc (δ : ℝ) * (((L : ℝ) + 1) * (n : ℝ))
        < (((n - 2 ^ m : ℕ) : ℝ) / (((L : ℝ) + 1) * (n : ℝ)))
          * (((L : ℝ) + 1) * (n : ℝ)) := by
          exact mul_lt_mul_of_pos_right h (by positivity)
      _ = ((n - 2 ^ m : ℕ) : ℝ) := by field_simp
  set t : ℕ := ⌈(1 - δ) * (n : ℝ≥0)⌉₊ with htdef
  by_cases hfull : t = n
  · -- the full-agreement edge: count ≤ L−1 ≤ (L−1)·n
    refine le_trans (epsMCACurve_rs_full_le φ (2 ^ m) L hL δ (by exact_mod_cast hfull)) ?_
    gcongr
    calc (L - 1 : ℕ) = (L - 1) * 1 := (mul_one _).symm
      _ ≤ (L - 1) * n := Nat.mul_le_mul_left _ hnpos
  · -- the stage-3 regime
    have htle : t ≤ n := by
      rw [htdef]
      refine Nat.ceil_le.mpr ?_
      calc (1 - δ) * (n : ℝ≥0) ≤ 1 * (n : ℝ≥0) := by
            gcongr; exact tsub_le_self
        _ = (n : ℝ≥0) := one_mul _
    have htn : t < n := lt_of_le_of_ne htle hfull
    have htge : ((1 : ℝ) - (δ : ℝ)) * (n : ℝ) ≤ (t : ℝ) := by
      have hceil : ((1 - δ) * (n : ℝ≥0) : ℝ≥0) ≤ (t : ℝ≥0) := Nat.le_ceil _
      have hc := (NNReal.coe_le_coe.mpr hceil)
      push_cast at hc
      by_cases hδ1 : (δ : ℝ) ≤ 1
      · rw [NNReal.coe_sub (by exact_mod_cast hδ1)] at hc
        push_cast at hc
        linarith [hc]
      · push Not at hδ1
        nlinarith [hnR, hδ1]
    have hnt : ((n - t : ℕ) : ℝ) ≤ (δ : ℝ) * (n : ℝ) := by
      rw [Nat.cast_sub htle]
      nlinarith [htge]
    have hregR : (((L + 1) * (n - t) : ℕ) : ℝ) < ((n - 2 ^ m : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub htle]
      calc ((L : ℝ) + 1) * ((n : ℝ) - (t : ℝ))
          ≤ ((L : ℝ) + 1) * ((δ : ℝ) * (n : ℝ)) := by
            have : ((n : ℝ) - (t : ℝ)) ≤ (δ : ℝ) * (n : ℝ) := by
              have := hnt
              rw [Nat.cast_sub htle] at this
              linarith
            nlinarith [hLR, this]
        _ = (δ : ℝ) * (((L : ℝ) + 1) * (n : ℝ)) := by ring
        _ < ((n - 2 ^ m : ℕ) : ℝ) := hδB'
    have hreg : (L + 1) * (n - t) < n - 2 ^ m + 1 := by
      have : ((L + 1) * (n - t) : ℕ) < (n - 2 ^ m : ℕ) := by exact_mod_cast hregR
      omega
    refine le_trans (epsMCACurve_rs_udr_le φ (2 ^ m) hk L hL δ
      (by exact_mod_cast htn) (by exact_mod_cast hreg)) ?_
    gcongr
    have h1 : (L + 1) * (n - t) ≤ n - 2 ^ m := Nat.lt_succ_iff.mp hreg
    have h2 : L * (n - t) ≤ (L + 1) * (n - t) :=
      Nat.mul_le_mul_right _ (Nat.le_succ L)
    have hLnt : L * (n - t) ≤ n := le_trans (le_trans h2 h1) (Nat.sub_le _ _)
    exact hLnt

end MutualCorrAgreement

#print axioms MutualCorrAgreement.mca_rsc_curve_udr

#print axioms MutualCorrAgreement.epsMCACurve_rs_full_le
