/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentIsolation
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersection
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentPairs

/-!
# CS25 #82, deliverable 2a (assembly): `E[N²] = |RS| · ∑_{e ∈ RS} I(e)`

Combining the pairs identity (`sum_sq_card_filter_eq_sum_pairs`), translation invariance
(`jointCoverCount_translation`), and the Reed–Solomon code's linearity, the second moment of the
codeword-cover count collapses to `|RS|` copies of the **ball-intersection sum** `∑_{e ∈ RS} I(e)`
with `I(e) = |B(0,δ) ∩ B(e,δ)| = jointCoverCount δ 0 e`.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Second moment as `|RS| · ∑_{e∈RS} I(e)`.** -/
theorem sum_sq_secondMomentCount_eq (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) :
    (∑ w : ι → F, (CodingTheory.secondMomentCount domain k δ w) ^ 2)
      = (univ.filter (fun c : ι → F => c ∈ (ReedSolomon.code domain k : Set (ι → F)))).card
        * ∑ e ∈ univ.filter (fun e : ι → F => e ∈ (ReedSolomon.code domain k : Set (ι → F))),
            jointCoverCount δ (0 : ι → F) e := by
  classical
  set C := (ReedSolomon.code domain k : Set (ι → F))
  -- Step 1: pairs identity for X w = #{c : c ∈ C ∧ δᵣ(w,c) ≤ δ}.
  have hpairs :
      (∑ w : ι → F, (CodingTheory.secondMomentCount domain k δ w) ^ 2)
        = ∑ c : ι → F, ∑ c' : ι → F,
            (univ.filter (fun w : ι → F =>
              (c ∈ C ∧ (relHammingDist w c : ENNReal) ≤ (δ : ENNReal))
                ∧ (c' ∈ C ∧ (relHammingDist w c' : ENNReal) ≤ (δ : ENNReal)))).card := by
    have := sum_sq_card_filter_eq_sum_pairs
      (Q := fun (w : ι → F) (c : ι → F) =>
        c ∈ C ∧ (relHammingDist w c : ENNReal) ≤ (δ : ENNReal))
    simpa [CodingTheory.secondMomentCount, C] using this
  rw [hpairs]
  -- Step 2: each inner count is `if c ∈ C ∧ c' ∈ C then jointCoverCount δ c c' else 0`.
  have hinner : ∀ c c' : ι → F,
      (univ.filter (fun w : ι → F =>
        (c ∈ C ∧ (relHammingDist w c : ENNReal) ≤ (δ : ENNReal))
          ∧ (c' ∈ C ∧ (relHammingDist w c' : ENNReal) ≤ (δ : ENNReal)))).card
        = if c ∈ C ∧ c' ∈ C then jointCoverCount δ c c' else 0 := by
    intro c c'
    by_cases hc : c ∈ C <;> by_cases hc' : c' ∈ C
    · simp only [hc, hc', true_and, and_true, if_true]
      rfl
    all_goals simp [hc, hc']
  simp_rw [hinner]
  -- Step 3: factor `c ∈ C` out of the inner sum and restrict to the code filter.
  have hstep : ∀ c : ι → F,
      (∑ c' : ι → F, if c ∈ C ∧ c' ∈ C then jointCoverCount δ c c' else 0)
        = if c ∈ C then (∑ c' ∈ univ.filter (fun c' : ι → F => c' ∈ C),
            jointCoverCount δ c c') else 0 := by
    intro c
    by_cases hc : c ∈ C
    · simp only [hc, true_and, if_true]
      rw [← Finset.sum_filter]
    · simp [hc]
  simp_rw [hstep]
  rw [← Finset.sum_filter]
  -- Step 4 + 5: translation + reindex (c' ↦ c'-c) + sum_const.
  have hreindex : ∀ c ∈ univ.filter (fun c : ι → F => c ∈ C),
      (∑ c' ∈ univ.filter (fun c' : ι → F => c' ∈ C), jointCoverCount δ c c')
        = ∑ e ∈ univ.filter (fun e : ι → F => e ∈ C), jointCoverCount δ (0 : ι → F) e := by
    intro c hc
    rw [Finset.mem_filter] at hc
    refine Finset.sum_nbij' (fun c' => c' - c) (fun e => e + c) ?_ ?_ ?_ ?_ ?_
    · intro c' hc'
      rw [Finset.mem_filter] at hc' ⊢
      exact ⟨mem_univ _, (ReedSolomon.code domain k).sub_mem hc'.2 hc.2⟩
    · intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨mem_univ _, (ReedSolomon.code domain k).add_mem he.2 hc.2⟩
    · intro c' _; simp
    · intro e _; simp
    · intro c' _; rw [jointCoverCount_translation δ c c']
  rw [Finset.sum_congr rfl hreindex, Finset.sum_const, smul_eq_mul]

end ArkLib.CS25
