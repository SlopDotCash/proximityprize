/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Stir.Combine

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Mirco Richter, Poulami Das (Least Authority), Aristotle
(Harmonic)
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination

import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.Basic
import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtractionVacuous
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ProximityPrize.Compatibility.UniformProbability
import ArkLib.ProofSystem.Stir.ProximityBound
import ArkLib.ProofSystem.Stir.ErrorBoundBridge
import ArkLib.ToMathlib.Polynomial.EvalExt


/-! Section 4.5 from STIR [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open BigOperators Finset NNReal Code

namespace Combine
variable {m : ℕ}
         {F : Type*} [Field F] [DecidableEq F]
         {ι : Type*}

open Finset
open BigOperators

private def total_terms (dstar : ℕ) (degs : Fin m → ℕ) := ∑ i, block_size dstar degs i

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι]

open scoped NNReal NNRat in
private lemma rho_add_inv_card_lt_one_sub_delta
  {n m : ℕ}
  {δ : ℝ≥0} {rho : ℚ≥0}
  (hδLt : δ < (min (1 - NNReal.sqrt rho)
    (1 - rho - 1 / (↑m))))
  (hrho : rho = n / (↑m : ℚ≥0)) :
  ↑rho + 1 / ↑(m) < 1 - δ := by
  all_goals first | infer_instance | simp_all +decide [lt_tsub_iff_left]
  ring_nf at *
  exact hδLt.2.trans_le' (by norm_cast)

private lemma succ_lt_one_sub_delta_mul_of_ratio_bound
  {n m : ℕ}
  {δ : ℝ≥0}
  (hm : 0 < m)
  (h : ↑n / ↑(m) + (↑(m))⁻¹ < 1 - δ) : ↑(n + 1) < (1 - δ) * m := by
 rw [← div_lt_iff₀ (by positivity)]
 convert h using 1
 push_cast
 ring

set_option maxHeartbeats 0 in
omit [DecidableEq F] [Fintype F] in
open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
lemma degree_lt_shifted_block_degree_of_large_agreement
    [Nonempty ι]
  {φ : ι ↪ F} {dstar m : ℕ}
  {fs : Fin m → ι → F} {degs : Fin m → ℕ} (hdegs : ∀ i, degs i ≤ dstar)
  {δ : ℝ≥0}
  (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
    (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
  {S : Finset ι}
  (hS_card : (1 - δ) * (Fintype.card ι) ≤ S.card)
  {v : (i : Fin m) → Fin (block_size dstar degs i) → Polynomial F}
  (hv_deg : ∀ i j, (v i j).degree < dstar)
  (hv_eval : ∀ i j, ∀ x ∈ S, (v i j).eval (φ x) = (φ x) ^ j.val * (fs i x))
  (i : Fin m)
  (j : Fin (block_size dstar degs i)) :
  (v i j).degree < degs i + j := by
  have hlt : dstar < Fintype.card ι := by
    by_contra contra
    aesop
      (add simp [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_right])
  rcases j with ⟨j, hj⟩
  simp only [block_size] at hj
  simp only [gt_iff_lt]
  generalize hj': (dstar - degs i) - j = j'
  revert j
  induction j' with
  | zero =>
    intro j hj hj'
    conv_rhs =>
      rw [show j = (dstar - degs i) by omega]
    rw [←WithBot.coe_natCast,
        show WithBot.some (dstar - degs i) = Nat.cast (dstar - degs i) by rfl,
        ←WithBot.coe_natCast, ←WithBot.coe_add, ←Nat.cast_add,
        Nat.add_sub_of_le (hdegs _)]
    exact hv_deg i ⟨j, hj⟩
  | succ j' ih =>
    intro j hj hj'
    have hj' : j = dstar - degs i - j' - 1 := by omega
    have h_fin : j + 1 < dstar - degs i + 1 := by omega
    specialize ih (j + 1) h_fin (by omega)
    let q : Polynomial F := Polynomial.X * v i ⟨j, hj⟩
    have hq_deg : q.degree < dstar + 1 := by
      rw [WithBot.lt_def]
      by_cases hv: v i ⟨j, hj⟩ = 0
      · aesop
      · right
        simp only [Polynomial.degree_mul, Polynomial.degree_X, q]
        rw [Polynomial.degree_eq_natDegree hv]
        exists (1 + (v i ⟨j ,hj⟩).natDegree)
        aesop
          (add unsafe (by rw [add_comm]))
          (add unsafe forward [Nat.add_lt_add_right])
          (add simp [Polynomial.natDegree_lt_iff_degree_lt])
    have hq_coincide :
      ∀ x ∈ S, q.eval (φ x) = (v i ⟨j + 1, h_fin⟩).eval (φ x) := by
      aesop
        (add simp [q])
        (add safe (by ring_nf))
    have hq_coincide :=
      Polynomial.eq_of_eval_eq_degree
        (q := v i ⟨j + 1, h_fin⟩)
        hq_deg (lt_trans (hv_deg _ _) <| by
          rw [WithBot.lt_def]
          right
          exists dstar, (dstar + 1)
          aesop
        ) (Finset.image φ S) (by {
          simp only [Nat.cast_id, ge_iff_le, Order.add_one_le_iff]
          rw [Finset.card_image_of_injective _ (fun x y hxy ↦ by aesop)]
          have h : ↑(rate (code φ dstar)) + 1 / ↑(Fintype.card ι) < 1 - δ :=
            rho_add_inv_card_lt_one_sub_delta
              (by simpa using hδLt)
              (by {
                simp only [rate]
                rfl
              })
          have h :=
            le_trans
              (le_of_lt <|
                succ_lt_one_sub_delta_mul_of_ratio_bound (m := Fintype.card ι)
                  (by simp) (by {
                    rw [ReedSolomon.rateOfLinearCode_eq_min_div,
                        min_eq_left (by omega)] at h
                    simpa using h
                  }))
              hS_card
          norm_cast at h
        })
        (by aesop)
    simp only [q] at hq_coincide
    rw [←hq_coincide] at ih
    simp only [Polynomial.degree_mul, Polynomial.degree_X, WithBot.coe_add, WithBot.coe_one] at ih
    rw [←add_assoc, add_comm 1] at ih
    exact (WithBot.add_lt_add_iff_right (by simp)).mp ih

open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
/-- **Lemma 4.13, UNCONDITIONAL in the small-field regime `q ≤ (total_terms − 1)·n`.**
The canonical `combine_theorem` now proves the stronger result without a coefficient residual.
This compatibility statement retains the former regime hypothesis for existing callers. -/
theorem combine_theorem_of_card_le
    [Nonempty ι] {φ : ι ↪ F} {dstar m : ℕ} [NeZero dstar]
    (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
    (δ : ℝ≥0) (hδPos : δ > 0)
    (_hq : (Fintype.card F : ℝ≥0)
      ≤ ((total_terms dstar degs - 1 : ℕ) : ℝ≥0) * (Fintype.card ι : ℝ≥0))
    (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                     (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
    (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
      (m * (dstar + 1) - ∑ i, degs i - 1) * ProximityGap.errorBound δ dstar φ) :
    ∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∃ v : Fin m → ι → F, ∀ i,
        v i ∈ (code φ (degs i)) ∧
          S ⊆ Finset.filter (fun j => v i j = fs i j) Finset.univ :=
by
  let : SampleableType F := SampleableType.ofFintype F
  apply combine_theorem fs degs hdegs (Nat.pos_of_ne_zero (NeZero.ne dstar)) δ hδPos hδLt
  rwa [← ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]


open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
/-- **Lemma 4.13, UNCONDITIONAL in the sharp interior regime `q ≤ (total_terms − 1)·dstar²·10⁷`.**
The canonical stronger result applies directly; the former regime hypothesis is retained. -/
theorem combine_theorem_of_card_le_e7
    [Nonempty ι] {φ : ι ↪ F} {dstar m : ℕ} [NeZero dstar]
    (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
    (δ : ℝ≥0) (hδPos : δ > 0)
    (_hq : (Fintype.card F : ℝ≥0)
      ≤ ((total_terms dstar degs - 1 : ℕ) : ℝ≥0) * ((dstar ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0))
    (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                     (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
    (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
      (m * (dstar + 1) - ∑ i, degs i - 1) * ProximityGap.errorBound δ dstar φ) :
    ∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∃ v : Fin m → ι → F, ∀ i,
        v i ∈ (code φ (degs i)) ∧
          S ⊆ Finset.filter (fun j => v i j = fs i j) Finset.univ :=
by
  let : SampleableType F := SampleableType.ofFintype F
  apply combine_theorem fs degs hdegs (Nat.pos_of_ne_zero (NeZero.ne dstar)) δ hδPos hδLt
  rwa [← ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]



open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
/-- **Lemma 4.13 with the `errStar`/`proximityError` threshold** — the exact error form
consumed by `stir_rbr_soundness`'s `ε_fold`/`ε_shift` bounds. Follows from `combine_theorem`
since `proximityError` dominates `(M−1)·errorBound` (`mul_errorBound_le_proximityError`). -/
theorem combine_theorem_proximityError
    [Nonempty ι] {φ : ι ↪ F} {dstar m : ℕ} [NeZero dstar]
    (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
    (δ : ℝ≥0) (hδPos : δ > 0)
    (_hStrictCoeff : ProximityGap.StrictCoeffPolysResidual
      (k := total_terms dstar degs - 1) (deg := dstar) (domain := φ) (δ := δ))
    (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                     (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
    (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
      proximityError F dstar (rate (code φ dstar)) δ (m * (dstar + 1) - ∑ i, degs i)) :
    ∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∃ v : Fin m → ι → F, ∀ i,
        v i ∈ (code φ (degs i)) ∧
          S ⊆ Finset.filter (fun j => v i j = fs i j) Finset.univ := by
  let : SampleableType F := SampleableType.ofFintype F
  rw [ProximityPrize.Compatibility.pmf_uniform_probability_eq_native] at hProb
  refine combine_theorem fs degs hdegs (Nat.pos_of_ne_zero (NeZero.ne dstar)) δ hδPos
    hδLt (lt_of_le_of_lt ?_ hProb)
  have hb := mul_errorBound_le_proximityError (ι := ι) (F := F)
    (deg := dstar) (m := m * (dstar + 1) - ∑ i, degs i) (domain := φ) (δ := δ)
  refine le_trans (le_of_eq ?_) (ENNReal.coe_le_coe.mpr hb)
  rw [ENNReal.coe_mul, ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_natCast,
    ENNReal.natCast_sub]
  norm_cast

open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
/-- **Lemma 4.13, `proximityError` threshold, UNCONDITIONAL small-field regime.** -/
theorem combine_theorem_proximityError_of_card_le
    [Nonempty ι] {φ : ι ↪ F} {dstar m : ℕ} [NeZero dstar]
    (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
    (δ : ℝ≥0) (hδPos : δ > 0)
    (hq : (Fintype.card F : ℝ≥0)
      ≤ ((total_terms dstar degs - 1 : ℕ) : ℝ≥0) * (Fintype.card ι : ℝ≥0))
    (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                     (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
    (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
      proximityError F dstar (rate (code φ dstar)) δ (m * (dstar + 1) - ∑ i, degs i)) :
    ∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∃ v : Fin m → ι → F, ∀ i,
        v i ∈ (code φ (degs i)) ∧
          S ⊆ Finset.filter (fun j => v i j = fs i j) Finset.univ :=
  combine_theorem_proximityError fs degs hdegs δ hδPos
    (ProximityGap.strictCoeffPolysResidual_of_card_le
      (Nat.pos_of_ne_zero (NeZero.ne dstar))
      (lt_of_lt_of_le hδLt (min_le_left _ _)) hq)
    hδLt hProb

end Combine

/- Axiom audit for the STIR combine residual front door (#24). -/
#print axioms Combine.combine_theorem
#print axioms Combine.combine_theorem_of_card_le
#print axioms Combine.combine_theorem_of_card_le_e7
#print axioms Combine.combine_theorem_proximityError
#print axioms Combine.combine_theorem_proximityError_of_card_le
