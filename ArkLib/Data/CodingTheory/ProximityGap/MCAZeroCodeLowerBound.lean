/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeExact

/-!
# The matching MCA lower bound for the zero code: `ε_mca(⊥, δ) ≥ (⌊δ·n⌋ + 1)/|F|`

This is the construction that matches `MCAZeroCodeUpperBound`, completing the exact
characterization `ε_mca(⊥, δ) = (⌊δn⌋+1)/|F|` whenever `⌊δn⌋+1 ≤ min(n, |F|)`.

**The optimal stack.** Pick a set `A ⊆ ι` of `k+1` coordinates (`k = ⌊δn⌋`) and a function `φ`
injective on `A`. On `A` put `u₁ = 1`, `u₀ = -φ`; off `A` put `u₀ = u₁ = 0`. Then for each `i₀ ∈ A`
the scalar `γ = φ i₀` is **bad**: the line `ℓ_γ` vanishes off `A` (the `n-(k+1)` common-zero
coordinates) and at `i₀` (`-φ i₀ + φ i₀ = 0`), a witness set of size `n - k ≥ (1-δ)n`, and `i₀`
is non-degenerate (`u₁ i₀ = 1 ≠ 0`). The `k+1` scalars `φ i₀` are distinct (`φ` injective on `A`),
so the stack has `≥ k+1` bad scalars and `ε_mca(⊥, δ) ≥ (k+1)/|F|`.

## References
- Matches `ProximityGap.MCAZeroCode.epsMCA_bot_le_floor_succ_div`.
- Issue #140 / #171.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeroCode

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

section LowerBound

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The optimal lower-bound stack: on `A`, `u₀ = -φ` and `u₁ = 1`; off `A`, both `0`. -/
noncomputable def slopeStack (A : Finset ι) (φ : ι → F) : WordStack F (Fin 2) ι :=
  fun k i => if k = 0 then (if i ∈ A then -(φ i) else 0) else (if i ∈ A then (1 : F) else 0)

@[simp] theorem slopeStack_zero (A : Finset ι) (φ : ι → F) (i : ι) :
    slopeStack A φ 0 i = (if i ∈ A then -(φ i) else 0) := by simp [slopeStack]

@[simp] theorem slopeStack_one (A : Finset ι) (φ : ι → F) (i : ι) :
    slopeStack A φ 1 i = (if i ∈ A then (1 : F) else 0) := by
  simp only [slopeStack]
  rw [if_neg (by decide : ¬ (1 : Fin 2) = 0)]

open Classical in
/-- Each slope `φ i₀` (for `i₀ ∈ A`) is a bad scalar of the optimal stack, provided the witness set
`(univ \ A) ∪ {i₀}` is large enough — guaranteed by `|A| ≤ δn + 1`. -/
theorem mcaEvent_slopeStack {δ : ℝ≥0} {A : Finset ι} {φ : ι → F}
    (hAcard : ((A.card : ℝ)) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) + 1)
    {i₀ : ι} (hi₀ : i₀ ∈ A) :
    mcaEvent (F := F) (Cbot : Set (ι → F)) δ (slopeStack A φ 0) (slopeStack A φ 1) (φ i₀) := by
  have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hAle : A.card ≤ Fintype.card ι := Finset.card_le_univ A
  refine ⟨Finset.univ \ (A.erase i₀), ?_, ⟨0, zero_mem_Cbot, ?_⟩, ?_⟩
  · -- `|univ \ (A.erase i₀)| = n - (|A|-1) ≥ (1-δ)n`.
    have hScard : (Finset.univ \ (A.erase i₀)).card = Fintype.card ι - (A.card - 1) := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Finset.card_erase_of_mem hi₀]
    have key : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)
        ≤ ((Finset.univ \ (A.erase i₀)).card : ℝ) := by
      rw [hScard, Nat.cast_sub (show A.card - 1 ≤ Fintype.card ι by omega), Nat.cast_sub hApos]
      by_cases hd : (δ : ℝ) ≤ 1
      · rw [NNReal.coe_sub (show δ ≤ 1 by exact_mod_cast hd)]
        push_cast
        nlinarith [hAcard]
      · push_neg at hd
        have hz : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
          rw [NNReal.coe_eq_zero, tsub_eq_zero_iff_le]; exact_mod_cast hd.le
        rw [hz]
        have haa : (A.card : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hAle
        push_cast; nlinarith [haa]
    rw [ge_iff_le, ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast]
    exact key
  · -- the line vanishes on the witness set
    intro i hi
    rw [Finset.mem_sdiff] at hi
    obtain ⟨_, hi2⟩ := hi
    rw [Finset.mem_erase, not_and] at hi2
    by_cases hiA : i ∈ A
    · have hii : i = i₀ := by by_contra hne; exact (hi2 hne) hiA
      subst hii
      simp [slopeStack_zero, slopeStack_one, hi₀]
    · simp [slopeStack_zero, slopeStack_one, hiA]
  · -- non-degeneracy at `i₀`
    rintro ⟨v₀, _hv₀, v₁, hv₁, hagree⟩
    have hv₁0 : v₁ = 0 := (mem_Cbot_iff v₁).mp hv₁
    have hi₀S : i₀ ∈ Finset.univ \ (A.erase i₀) := by
      rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, by simp⟩
    have hc := (hagree i₀ hi₀S).2
    rw [hv₁0] at hc
    simp only [Pi.zero_apply, slopeStack_one, if_pos hi₀] at hc
    exact absurd hc zero_ne_one

open Classical in
/-- **MCA lower bound for the zero code:** `ε_mca(⊥, δ) ≥ (⌊δ·n⌋ + 1)/|F|`, whenever
`⌊δn⌋ + 1 ≤ |ι|` and `⌊δn⌋ + 1 ≤ |F|`. With `epsMCA_bot_le_floor_succ_div` this pins
`ε_mca(⊥, δ) = (⌊δn⌋+1)/|F|` exactly in this regime. -/
theorem epsMCA_bot_ge_floor_succ_div {δ : ℝ≥0}
    (hkn : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 ≤ Fintype.card ι)
    (hkF : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 ≤ Fintype.card F) :
    ((⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ := by
  set k : ℕ := ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ with hk
  -- choose `A ⊆ ι` of size `k+1` and `φ` injective on `A`.
  obtain ⟨A, _hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := k + 1)
      (by simpa [Finset.card_univ] using hkn)
  have hAcard_le : ((A.card : ℝ)) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) + 1 := by
    rw [hAcard]; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ (δ:ℝ) * (Fintype.card ι:ℝ) by positivity)
    rw [← hk] at this; linarith
  obtain ⟨ψ⟩ : Nonempty ((A : Finset ι) ↪ F) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_coe, hAcard]; exact hkF
  let φ : ι → F := fun i => if h : i ∈ A then ψ ⟨i, h⟩ else 0
  have hφinj : Set.InjOn φ A := by
    intro i hi i' hi' heq
    have e1 : φ i = ψ ⟨i, hi⟩ := dif_pos hi
    have e2 : φ i' = ψ ⟨i', hi'⟩ := dif_pos hi'
    rw [e1, e2] at heq
    exact Subtype.ext_iff.mp (ψ.injective heq)
  -- the `k+1` distinct slopes `φ i₀` are all bad.
  have hsub : A.image φ ⊆
      Finset.filter (fun γ : F => mcaEvent (F := F) (Cbot : Set (ι → F)) δ
        (slopeStack A φ 0) (slopeStack A φ 1) γ) Finset.univ := by
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨i₀, hi₀, rfl⟩ := hγ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mcaEvent_slopeStack hAcard_le hi₀⟩
  have hcard_image : (A.image φ).card = k + 1 := by
    rw [Finset.card_image_of_injOn hφinj, hAcard]
  -- so the stack has `≥ k+1` bad scalars; average over `γ`.
  have hBge : (k + 1 : ℕ) ≤
      (Finset.filter (fun γ : F => mcaEvent (F := F) (Cbot : Set (ι → F)) δ
        (slopeStack A φ 0) (slopeStack A φ 1) γ) Finset.univ).card := by
    rw [← hcard_image]; exact Finset.card_le_card hsub
  -- `Pr_γ[mcaEvent] = |B|/|F| ≥ (k+1)/|F|`, and `≤ ε_mca`.
  have hprob : ((k + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (Cbot : Set (ι → F)) δ
          (slopeStack A φ 0) (slopeStack A φ 1) γ] := by
    rw [prob_uniform_eq_card_filter_div_card]
    have hcast : ((k + 1 : ℕ) : ℝ≥0∞) ≤
        (((Finset.filter (fun γ : F => mcaEvent (F := F) (Cbot : Set (ι → F)) δ
          (slopeStack A φ 0) (slopeStack A φ 1) γ) Finset.univ).card : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hBge
    simp only [ENNReal.coe_natCast] at hcast ⊢
    gcongr
  refine le_trans hprob ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (Cbot : Set (ι → F)) δ (u 0) (u 1) γ])
    (slopeStack A φ)

end LowerBound

/-! ## Source audit -/

#print axioms mcaEvent_slopeStack
#print axioms epsMCA_bot_ge_floor_succ_div

end ProximityGap.MCAZeroCode
