/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ErrStarArith
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArithmetic
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Unit (3) glue: `johnsonBoundReal ≤` the conjecture's `errStar`, instantiated

`Hab25ErrStarArith.lean` proved the arithmetic core of the comparison in `√`-substituted
variables. This file supplies the convention glue:

* `rate_smoothCode_coe` — the rate identity `(rate (smoothCode φ m) : ℝ) = 2^m/n` from the
  in-tree RS dimension formula (`dim_eq_deg_of_le'`);
* `johnsonM_ceil_bound` — the ceiling fact at `η := μ`
  (`μ := min(1−√ρ−δ, √ρ/20)`): `u·(M+½) ≤ s + (7/2)·u`, `u = 2μ`, `s = √ρ₊` — the `hPu`
  input of the arithmetic core;
* **`johnsonBoundReal_le_errStar_real`** — the real-level comparison: for
  `2^m ≤ n` and `0 < δ < 1 − √(2^m/n)`,

    `johnsonBoundReal φ (2^m) μ.toNNReal δ ≤ 2^{2m} / (|F| · (2μ)⁷)`

  — exactly the (pair-case) conjecture `errStar` with `ρ = 2^m/n` and
  `2^{2m} = (ρn)²` *exactly*.

The earlier-flagged `ρ₊` vs `ρ` range wrinkle dissolves: our composition never needs
`InJohnsonRange` — `η` enters `johnsonBoundReal` only through the ceiling `M`, so
`η := μ(δ)` is admissible outright, with no large-`n` side condition.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open scoped NNReal ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

omit [DecidableEq ι₀] [Fintype F₀] in
/-- **The rate identity**: for `2^m ≤ n`, the rate of the smooth RS code is exactly
`2^m/n` (as a real number). -/
theorem rate_smoothCode_coe (φ : ι₀ ↪ F₀) [ReedSolomon.Smooth φ] (m : ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι₀) :
    ((LinearCode.rate (ReedSolomon.smoothCode φ m) : ℚ≥0) : ℝ) =
      (2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ) := by
  have hdim : LinearCode.dim (ReedSolomon.smoothCode φ m) = 2 ^ m :=
    ReedSolomon.dim_eq_deg_of_le' hk
  rw [LinearCode.rate, hdim]
  have hlen : LinearCode.length (ReedSolomon.smoothCode φ m) = Fintype.card ι₀ := rfl
  rw [hlen]
  push_cast
  ring

/-- **The ceiling fact for the GS multiplicity parameter** at `η := μ`: with
`u := 2μ > 0` and `s := ρ₊^{1/2}`, `u·(M+½) ≤ s + (7/2)·u`. -/
theorem johnsonM_ceil_bound {n k : ℕ} {μ s : ℝ} (hμ0 : 0 < μ)
    (hs : (hab25RhoPlus n k) ^ ((1 : ℝ) / 2) = s) (hs0 : 0 ≤ s) :
    (2 * μ) * (hab25M n k μ.toNNReal + 1 / 2) ≤ s + (7 / 2) * (2 * μ) := by
  have hμcoe : ((μ.toNNReal : ℝ≥0) : ℝ) = μ := Real.coe_toNNReal μ hμ0.le
  have hMle : hab25M n k μ.toNNReal ≤ s / (2 * μ) + 3 := by
    rw [hab25M, hs, hμcoe]
    have hceil : (⌈s / (2 * μ)⌉ : ℝ) ≤ s / (2 * μ) + 1 :=
      le_of_lt (Int.ceil_lt_add_one _)
    have hpos : (0 : ℝ) ≤ s / (2 * μ) := by positivity
    refine max_le ?_ ?_
    · linarith
    · linarith
  have h2μ : (0 : ℝ) < 2 * μ := by linarith
  have hmul := mul_le_mul_of_nonneg_left hMle h2μ.le
  have hcancel : (2 * μ) * (s / (2 * μ) + 3) = s + 6 * μ := by
    field_simp
    ring
  calc (2 * μ) * (hab25M n k μ.toNNReal + 1 / 2)
      = (2 * μ) * hab25M n k μ.toNNReal + μ := by ring
    _ ≤ (2 * μ) * (s / (2 * μ) + 3) + μ := by linarith
    _ = s + 6 * μ + μ := by rw [hcancel]
    _ ≤ s + (7 / 2) * (2 * μ) := by linarith

omit [DecidableEq ι₀] [DecidableEq F₀] in
/-- **The real-level comparison**: for `2^m ≤ n` and `δ < 1 − √(2^m/n)`, with
`μ := min (1 − √(2^m/n) − δ) (√(2^m/n)/20)`,

  `johnsonBoundReal φ (2^m) μ.toNNReal δ ≤ 2^{2m} / (|F| · (2μ)⁷)`

— the (pair-case) WHIR Johnson-conjecture error with `ρ = 2^m/n`. -/
theorem johnsonBoundReal_le_errStar_real
    (φ : ι₀ ↪ F₀) (m : ℕ) (hk : 2 ^ m ≤ Fintype.card ι₀)
    (δ : ℝ≥0)
    (hδB : (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ))) :
    Hab25Johnson.johnsonBoundReal (F := F₀) (ι := ι₀) φ (2 ^ m)
      (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) - (δ : ℝ))
        (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) / 20)).toNNReal δ ≤
      (2 ^ (2 * m) : ℝ) /
        ((Fintype.card F₀ : ℝ) *
          (2 * min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) / 20)) ^ 7) := by
  classical
  rw [johnsonBoundReal_eq]
  set n : ℕ := Fintype.card ι₀ with hn_def
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hnR0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have h2m : (1 : ℝ) ≤ (2 ^ m : ℝ) := one_le_pow₀ (by norm_num)
  have hF0 : (0 : ℝ) < (Fintype.card F₀ : ℝ) := by exact_mod_cast Fintype.card_pos
  set ρG : ℝ := (2 ^ m : ℝ) / (n : ℝ) with hρG_def
  have hρG0 : 0 < ρG := by positivity
  have hρG1 : ρG ≤ 1 := by
    rw [hρG_def, div_le_one hnR0]
    exact_mod_cast hk
  set r : ℝ := Real.sqrt ρG with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hρG0
  have hr1 : r ≤ 1 := by
    rw [hr_def, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hρG1
  have hr2 : r ^ 2 = ρG := Real.sq_sqrt hρG0.le
  set μ : ℝ := min (1 - r - (δ : ℝ)) (r / 20) with hμ_def
  have hμ0 : 0 < μ := by
    rw [hμ_def]
    refine lt_min ?_ (by positivity)
    linarith
  set u : ℝ := 2 * μ with hu_def
  have hu0 : 0 < u := by rw [hu_def]; linarith
  have hur : 10 * u ≤ r := by
    have hμr : μ ≤ r / 20 := min_le_right _ _
    rw [hu_def]
    linarith
  -- `ρ₊` and its square root
  set ρP : ℝ := hab25RhoPlus n (2 ^ m) with hρP_def
  have hρP0 : 0 < ρP := hab25RhoPlus_pos hn0 _
  set s : ℝ := Real.sqrt ρP with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hρP0
  have hs2 : s ^ 2 = ρP := Real.sq_sqrt hρP0.le
  have hsr : ρP ^ ((1 : ℝ) / 2) = s := by
    rw [hs_def, Real.sqrt_eq_rpow]
  have hρGP : ρG ≤ ρP := by
    rw [hρG_def, hρP_def, hab25RhoPlus]
    push_cast
    have h1n : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hrs : r ≤ s := by
    rw [hr_def, hs_def]
    exact Real.sqrt_le_sqrt hρGP
  have hsP2 : s ^ 2 ≤ 2 * r ^ 2 := by
    rw [hs2, hr2, hρP_def, hρG_def, hab25RhoPlus]
    push_cast
    have key : ((2 : ℝ) ^ m + 1) / (n : ℝ) ≤ (2 * 2 ^ m) / (n : ℝ) := by
      gcongr
      linarith
    calc (2 : ℝ) ^ m / (n : ℝ) + 1 / (n : ℝ)
        = ((2 : ℝ) ^ m + 1) / (n : ℝ) := by ring
      _ ≤ (2 * 2 ^ m) / (n : ℝ) := key
      _ = 2 * ((2 : ℝ) ^ m / (n : ℝ)) := by ring
  -- the multiplicity parameter
  have hceil := johnsonM_ceil_bound (n := n) (k := 2 ^ m) hμ0 hsr hs0.le
  set M : ℝ := hab25M n (2 ^ m) μ.toNNReal with hM_def
  set P : ℝ := M + 1 / 2 with hP_def
  have hM3 : (3 : ℝ) ≤ M := hab25M_ge_three n _ _
  have hP72 : (7 : ℝ) / 2 ≤ P := by rw [hP_def]; linarith
  have hPu : u * P ≤ s + (7 / 2) * u := by
    rw [hu_def, hP_def]
    exact hceil
  have hδ1 : (δ : ℝ) ≤ 1 := by linarith
  -- the arithmetic core
  have hcore := johnsonBound_term_le_errStar_term (s := s) (r := r) (u := u)
    (n := (n : ℝ)) (δ := (δ : ℝ)) (P := P)
    hr0 hr1 hrs hsP2 hu0 hur hnR δ.coe_nonneg hδ1 hP72 hPu
  -- convert the powers and assemble
  have hρP32 : ρP ^ ((3 : ℝ) / 2) = s ^ 2 * s := by
    have h32 : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
    rw [h32, Real.rpow_add hρP0, Real.rpow_one, hsr, ← hs2]
  have hpow : (r ^ 2 * (n : ℝ)) ^ 2 = (2 : ℝ) ^ (2 * m) := by
    rw [hr2, hρG_def, div_mul_cancel₀ _ (ne_of_gt hnR0), ← pow_mul, mul_comm m 2]
  have hsplit : (2 : ℝ) ^ (2 * m) / ((Fintype.card F₀ : ℝ) * u ^ 7) =
      ((r ^ 2 * (n : ℝ)) ^ 2 / u ^ 7) / (Fintype.card F₀ : ℝ) := by
    rw [hpow, div_div, mul_comm ((Fintype.card F₀ : ℝ)) (u ^ 7)]
  rw [hρP32, hsr, ← hs2, hsplit]
  gcongr

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.rate_smoothCode_coe
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonM_ceil_bound
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonBoundReal_le_errStar_real
