/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAJohnsonCount

/-!
# Issue #244 — the `hwitAll` common-center clustering hypothesis, audited

`ProximityGap.MCAGS.rs_epsMCA_le_johnson_ceil_of_hwit`
(`MCAJohnsonCount.lean`) is conditional on a clustering hypothesis `hwitAll`:
for the pencil there is a single active coordinate `x`, a center word `w`, and a sub-Johnson
radius `e` such that **every** line-close scalar `γ` is explained by a codeword `c` with
`Δ₀(c, w) ≤ e` and `c x = u₀ x + γ·u₁ x`. Issue #244 claims this is refutable past the
half-Johnson radius.

This file resolves the audit **end-to-end**, and in doing so corrects the issue's own
proposed Lean target.

## The concrete instance

`F = GF(5)`, `ι = Fin 4`, `k = 2` (so `ρ = 1/2`, RS minimum distance `n − k + 1 = 3`),
domain `i ↦ i`. The pencil is the *constant pencil* `u 0 = 0`, `u 1 = 1`: every line point
`u 0 + γ • u 1` is the constant word `γ`, which lies in `ReedSolomon.code domain 2` (constant
polynomials have degree `0 < 2`). Hence **all `|F| = 5` scalars `γ` are line-close** (relative
distance `0 ≤ δ`). The band condition is met at `δ = 1/5`:
`(1 − √ρ)/2 ≈ 0.1464 < 0.2 < 0.2929 ≈ 1 − √ρ`.

## Two results, and the corrected statement

* `issue244_literal_target_satisfiable` — the issue's **literal** Lean target is *false*. The
  proposed statement puts `∃ e : ℕ` *inside* the negation, gated only by
  `0 < johnsonDenom n (n−k+1) e`. But `johnsonDenom 4 3 e = (4−e)² − 4 > 0` holds not only for
  `e ∈ {0, 1}` (the genuine Johnson window) but **also for every `e ≥ 7`** — a spurious upper
  branch of the quadratic where `e` already exceeds `n = 4`, so the radius-`e` ball is the
  *entire* code and the ball-cap argument collapses. Concretely `e = 7` gives
  `johnsonDenom 4 3 7 = 5 > 0`, and the witness `c := u 0 + γ • u 1` (the line point itself)
  satisfies `Δ₀(c, w) ≤ 4 ≤ 7` and `c x = u 0 x + γ·u 1 x` for **every** `γ`. So the inner
  existential the issue wanted to negate is in fact *satisfiable*; its negation is false. The
  refutation mechanism in the issue silently assumed `e ≤ n`.

* `hwitAll_common_center_refutable` — the **corrected** refutation, with the genuine Johnson
  constraint `e ≤ Fintype.card ι` reinstated. With `e ≤ 4` and `johnsonDenom 4 3 e > 0` the only
  surviving radii are `e ∈ {0, 1}`, and we fix `e = 1`. Then the RS Johnson list-size cap
  (`rs_card_ball_le`, via `rs_lineCloseCount_le_johnson`) gives
  `#{γ line-close} ≤ 4·3 / johnsonDenom 4 3 1 = 12/5 = 2.4`, while the constant pencil makes
  *all* `5` scalars line-close: `5 ≤ 2.4`, a contradiction. So **no common center reaches the
  full Johnson radius**, confirming the issue's mathematical claim.

Net: the single-common-center technique cannot reach the full Johnson radius (the issue is
mathematically right), but its proposed encoding dropped `e ≤ n` and is therefore literally
refutable in the wrong direction (the encoding is buggy). Both facts are machine-checked here.
-/

open scoped BigOperators NNReal
open ProximityGap ProximityGap.MCAGS

namespace ProximityGap.GrandChallenge244

set_option linter.unusedSectionVars false

/-- `GF(5)` is a field. -/
instance primeFact_CommonCenterJohnsonRefutation_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The evaluation domain `i ↦ i : Fin 4 ↪ ZMod 5`. Injective since `i.val < 4 < 5`. -/
def domain₄ : Fin 4 ↪ ZMod 5 := ⟨fun i => (i.val : ZMod 5), by decide⟩

/-- The constant pencil: `u 0 = 0`, `u 1 = 1`. -/
def uConst : Code.WordStack (ZMod 5) (Fin 2) (Fin 4) :=
  ![ReedSolomon.constantCode 0 (Fin 4), ReedSolomon.constantCode 1 (Fin 4)]

@[simp] lemma uConst_zero_apply (a : Fin 4) : uConst 0 a = 0 := rfl
@[simp] lemma uConst_one_apply (a : Fin 4) : uConst 1 a = 1 := rfl

/-- Each line point of the constant pencil is the constant codeword `γ`. -/
lemma line_eq_const (γ : ZMod 5) :
    uConst 0 + γ • uConst 1 = ReedSolomon.constantCode γ (Fin 4) := by
  funext a
  simp [ReedSolomon.constantCode]

/-- Each line point of the constant pencil lies in the Reed–Solomon code. -/
lemma line_mem (γ : ZMod 5) :
    (uConst 0 + γ • uConst 1) ∈ (ReedSolomon.code domain₄ 2 : Set (Fin 4 → ZMod 5)) := by
  rw [line_eq_const]
  exact ReedSolomon.constantCode_mem_code

/-- Every scalar is line-close: the relative distance from each line point to the code is `0`. -/
lemma line_close (γ : ZMod 5) (δ : ℝ≥0) :
    δᵣ(uConst 0 + γ • uConst 1, (ReedSolomon.code domain₄ 2 : Set (Fin 4 → ZMod 5)))
      ≤ (δ : ENNReal) := by
  have hle := Code.relDistFromCode_le_relDist_to_mem
    (uConst 0 + γ • uConst 1) (uConst 0 + γ • uConst 1) (line_mem γ)
  refine le_trans (le_trans hle (le_of_eq ?_)) (zero_le _)
  have hz : Code.relHammingDist (uConst 0 + γ • uConst 1) (uConst 0 + γ • uConst 1) = 0 := by
    simp [Code.relHammingDist]
  rw [hz, ENNReal.coe_NNRat_coe_NNReal]
  simp

/-- **The issue's literal target is false: the inner existential is satisfiable.**
The proposed statement gates `e` only by `0 < johnsonDenom`, which the spurious upper branch
`e = 7` satisfies (`johnsonDenom 4 3 7 = 5 > 0`) while making the radius-`e` ball the whole code.
The line point itself is then the required witness for *every* `γ`, so the negation fails. -/
theorem issue244_literal_target_satisfiable :
    ∃ (ι F : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : DecidableEq ι)
      (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (k : ℕ) (_ : NeZero k)
      (domain : ι ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι),
      ((1 - Real.sqrt ((k : ℝ) / Fintype.card ι)) / 2 < (δ : ℝ)) ∧
      ((δ : ℝ) < 1 - Real.sqrt ((k : ℝ) / Fintype.card ι)) ∧
      (∃ x : ι, u 1 x ≠ 0 ∧ ∃ w : ι → F, ∃ e : ℕ,
        0 < ArkLib.JohnsonBound.johnsonDenom (Fintype.card ι) (Fintype.card ι - k + 1) e ∧
        ∀ γ : F, δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
          ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)),
            Δ₀(c, w) ≤ e ∧ c x = u 0 x + γ * u 1 x) := by
  refine ⟨Fin 4, ZMod 5, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 2, inferInstance, domain₄, 1 / 5, uConst, ?_, ?_, ?_⟩
  · -- lower band bound: (1 - √(2/4))/2 < 1/5
    have hcardR : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
    rw [hcardR, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num,
      show (((1 : ℝ≥0) / 5 : ℝ≥0) : ℝ) = (1 : ℝ) / 5 from by norm_num]
    have hs2 : Real.sqrt ((2 : ℝ) / 4) ^ 2 = 2 / 4 := Real.sq_sqrt (by norm_num)
    have hsn : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) / 4) := Real.sqrt_nonneg _
    have h35 : (3 : ℝ) / 5 < Real.sqrt ((2 : ℝ) / 4) := by nlinarith [hs2, hsn]
    linarith [h35]
  · -- upper band bound: 1/5 < 1 - √(2/4)
    have hcardR : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
    rw [hcardR, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num,
      show (((1 : ℝ≥0) / 5 : ℝ≥0) : ℝ) = (1 : ℝ) / 5 from by norm_num]
    have hs2 : Real.sqrt ((2 : ℝ) / 4) ^ 2 = 2 / 4 := Real.sq_sqrt (by norm_num)
    have hsn : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) / 4) := Real.sqrt_nonneg _
    have h45 : Real.sqrt ((2 : ℝ) / 4) < 4 / 5 := by nlinarith [hs2, hsn]
    linarith [h45]
  · -- the inner existential: x = 1, w = 0, e = 7 (spurious upper branch of johnsonDenom)
    refine ⟨1, ?_, 0, 7, ?_, ?_⟩
    · -- u 1 1 = 1 ≠ 0
      simp
    · -- 0 < johnsonDenom 4 3 7 = 5
      simp only [Fintype.card_fin, ArkLib.JohnsonBound.johnsonDenom]; norm_num
    · -- witness for every γ: the line point itself
      intro γ _
      refine ⟨uConst 0 + γ • uConst 1, line_mem γ, ?_, ?_⟩
      · exact le_trans hammingDist_le_card_fintype (by rw [Fintype.card_fin]; norm_num)
      · simp [Pi.add_apply, Pi.smul_apply]

/-- **The corrected refutation (with the genuine Johnson constraint `e ≤ Fintype.card ι`).**
At the band `δ = 1/5 ∈ ((1−√ρ)/2, 1−√ρ)` with `ρ = 1/2`, *no* common center `(x, w)` at a fixed
in-window radius `e ≤ n` clusters the constant pencil: the RS Johnson list-size cap forces
`#{line-close γ} ≤ 12/5 = 2.4`, but the constant pencil makes all `5` scalars line-close.
This confirms the single-common-center technique cannot reach the full Johnson radius. -/
theorem hwitAll_common_center_refutable :
    ∃ (ι F : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : DecidableEq ι)
      (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (k : ℕ) (_ : NeZero k)
      (domain : ι ↪ F) (δ : ℝ≥0) (e : ℕ) (u : Code.WordStack F (Fin 2) ι),
      ((1 - Real.sqrt ((k : ℝ) / Fintype.card ι)) / 2 < (δ : ℝ)) ∧
      ((δ : ℝ) < 1 - Real.sqrt ((k : ℝ) / Fintype.card ι)) ∧
      e ≤ Fintype.card ι ∧
      0 < ArkLib.JohnsonBound.johnsonDenom (Fintype.card ι) (Fintype.card ι - k + 1) e ∧
      ¬ (∃ x : ι, u 1 x ≠ 0 ∧ ∃ w : ι → F,
          ∀ γ : F, δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
            ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)),
              Δ₀(c, w) ≤ e ∧ c x = u 0 x + γ * u 1 x) := by
  classical
  refine ⟨Fin 4, ZMod 5, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 2, inferInstance, domain₄, 1 / 5, 1, uConst, ?_, ?_, ?_, ?_, ?_⟩
  · -- lower band bound
    have hcardR : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
    rw [hcardR, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num,
      show (((1 : ℝ≥0) / 5 : ℝ≥0) : ℝ) = (1 : ℝ) / 5 from by norm_num]
    have hs2 : Real.sqrt ((2 : ℝ) / 4) ^ 2 = 2 / 4 := Real.sq_sqrt (by norm_num)
    have hsn : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) / 4) := Real.sqrt_nonneg _
    have h35 : (3 : ℝ) / 5 < Real.sqrt ((2 : ℝ) / 4) := by nlinarith [hs2, hsn]
    linarith [h35]
  · -- upper band bound
    have hcardR : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
    rw [hcardR, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num,
      show (((1 : ℝ≥0) / 5 : ℝ≥0) : ℝ) = (1 : ℝ) / 5 from by norm_num]
    have hs2 : Real.sqrt ((2 : ℝ) / 4) ^ 2 = 2 / 4 := Real.sq_sqrt (by norm_num)
    have hsn : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) / 4) := Real.sqrt_nonneg _
    have h45 : Real.sqrt ((2 : ℝ) / 4) < 4 / 5 := by nlinarith [hs2, hsn]
    linarith [h45]
  · -- e = 1 ≤ card (Fin 4) = 4
    rw [Fintype.card_fin]; norm_num
  · -- 0 < johnsonDenom 4 3 1 = 5
    simp only [Fintype.card_fin, ArkLib.JohnsonBound.johnsonDenom]; norm_num
  · -- the refutation proper
    rintro ⟨x, hx, w, hwit⟩
    -- enumerate the RS code as a Finset
    set Cset : Finset (Fin 4 → ZMod 5) :=
      Finset.univ.filter (· ∈ (ReedSolomon.code domain₄ 2 : Set (Fin 4 → ZMod 5))) with hCsetdef
    have hCset : (↑Cset : Set (Fin 4 → ZMod 5))
        = (ReedSolomon.code domain₄ 2 : Set (Fin 4 → ZMod 5)) := by
      ext c; simp [hCsetdef]
    -- transport the per-`γ` witness into the `Finset` form expected by the count lemma
    have hwit' : ∀ γ : ZMod 5,
        δᵣ(uConst 0 + γ • uConst 1, (ReedSolomon.code domain₄ 2 : Set (Fin 4 → ZMod 5))) ≤ (1 / 5 : ℝ≥0) →
        ∃ c ∈ Cset, Δ₀(c, w) ≤ 1 ∧ c x = uConst 0 x + γ * uConst 1 x := by
      intro γ hγ
      obtain ⟨c, hc, hd, heq⟩ := hwit γ hγ
      exact ⟨c, by rw [← Finset.mem_coe, hCset]; exact hc, hd, heq⟩
    -- the Johnson count bound
    have hk : (2 : ℕ) ≤ Fintype.card (Fin 4) := by rw [Fintype.card_fin]; norm_num
    have hen : (1 : ℕ) ≤ Fintype.card (Fin 4) := by rw [Fintype.card_fin]; norm_num
    have hJ : 0 < ArkLib.JohnsonBound.johnsonDenom
        (Fintype.card (Fin 4)) (Fintype.card (Fin 4) - 2 + 1) 1 := by
      simp only [Fintype.card_fin, ArkLib.JohnsonBound.johnsonDenom]; norm_num
    have key := rs_lineCloseCount_le_johnson (k := 2) (domain := domain₄)
      hk (1 / 5) 1 x uConst hx w hen hJ Cset hCset hwit'
    -- all `5` scalars are line-close, so the count is `5`
    have hfilter : (Finset.univ.filter (fun γ : ZMod 5 =>
        δᵣ(uConst 0 + γ • uConst 1,
          (ReedSolomon.code domain₄ 2 : Set (Fin 4 → ZMod 5))) ≤ (1 / 5 : ℝ≥0)))
        = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro γ _; exact line_close γ (1 / 5)
    rw [hfilter, Finset.card_univ] at key
    -- `5 ≤ 12/5`, contradiction
    have hc5 : ((Fintype.card (ZMod 5) : ℕ) : ℚ) = 5 := by simp [ZMod.card]
    have hM : (Fintype.card (Fin 4) : ℚ) * ((Fintype.card (Fin 4) - 2 + 1 : ℕ) : ℚ)
        / ArkLib.JohnsonBound.johnsonDenom
            (Fintype.card (Fin 4)) (Fintype.card (Fin 4) - 2 + 1) 1 = 12 / 5 := by
      simp only [Fintype.card_fin, ArkLib.JohnsonBound.johnsonDenom]; norm_num
    rw [hc5, hM] at key
    linarith [key]

end ProximityGap.GrandChallenge244
