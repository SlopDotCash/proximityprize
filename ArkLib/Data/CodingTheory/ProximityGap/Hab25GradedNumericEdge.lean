/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Hab25K4Seam

/-!
# The graded Johnson numeric edge — the beyond-window chain closes modulo K4 alone

The K4 seam (`Hab25K4Seam.lean`) consumes the numeric comparison
`((D/(k−1)+1)·T : ℝ)/|F| ≤ johnsonBoundReal` at the graded budget
`T = n·|cI|·(D/(k−1))`. This file **proves that comparison outright**:

* `graded_budget_core` — the division-free arithmetic core, in the `√`-substituted
  variables `y := D/(k−1)`, `c := |cI|`, `r := √ρ`, `sp := √ρ₊`, `M := hab25M`:
  `3·sp³·((y+1)·c·y) ≤ 2·(M+½)⁵` from `y·r ≤ (7/6)(M+½)` (the floor of the GS degree
  bound), `r ≤ (2/7)(M+½)`, `sp ≤ (15/14)·r` (`ρ₊ ≤ (225/196)·ρ` at `k ≥ 7`),
  `c ≤ M²`, `r ≤ 9/10`, `M ≥ 3` — the margins are ≥ 70 % at the worst corner;
* `graded_budget_le_ell_budget` — the `ℓ`-budget form
  `(D/(k−1)+1)·|cI|·(D/(k−1)) ≤ 2(M+½)⁵/(3ρ₊^{3/2})`, fed to the in-tree
  `nat_mul_card_div_le_johnsonBoundReal`;
* `graded_budget_div_le_johnsonBoundReal` — the exact `hNdiv` shape of
  `johnsonNumericBound_of_K4_graded`;
* **`johnsonNumericBound_of_K4_graded_closed`** — the capstone: **K4 alone** (plus the
  structural hypotheses `k ≥ 7`, `k+1 ≤ n`, `√ρ ≤ 9/10`, `m = hab25M`) discharges the
  `JohnsonNumericBound` residual. With `Hab25WhirBridge.lean`, the entire beyond-window
  #302 chain is now the single implication K4 ⟹ WHIR pair MCA, with **no numeric side
  conditions** — matching the already-unconditional window regime.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

/-- `x^{3/2} = (√x)³` for nonnegative reals — the rpow-elimination bridge. -/
lemma rpow_three_halves_eq_sqrt_cube {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((3 : ℝ) / 2) = (Real.sqrt x) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) 3,
    ← Real.rpow_mul hx]
  norm_num

/-- The constraint-index count is at most `m²`. -/
lemma constraintIndices_card_le (m : ℕ) :
    (GuruswamiSudan.constraintIndices m).card ≤ m * m := by
  unfold GuruswamiSudan.constraintIndices
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [show (Finset.range m).product (Finset.range m) =
      Finset.range m ×ˢ Finset.range m from rfl,
    Finset.card_product, Finset.card_range]

/-- **The division-free arithmetic core** of the graded Johnson numeric edge:
`3·sp³·((y+1)·c·y) ≤ 2·(M+½)⁵` in the `√`-substituted variables. -/
theorem graded_budget_core {y c r sp M : ℝ}
    (hy0 : 0 ≤ y) (hc0 : 0 ≤ c) (hr0 : 0 < r) (hsp0 : 0 ≤ sp)
    (hM3 : 3 ≤ M) (hcM : c ≤ M ^ 2) (hr9 : r ≤ 9 / 10)
    (hyr : y * r ≤ (7 / 6) * (M + 1 / 2))
    (hrM : r ≤ (2 / 7) * (M + 1 / 2))
    (hsp : sp ≤ (15 / 14) * r) :
    3 * sp ^ 3 * ((y + 1) * c * y) ≤ 2 * (M + 1 / 2) ^ 5 := by
  have hM0 : (0 : ℝ) < M + 1 / 2 := by linarith
  -- the combined fold-degree bound: `(y+1)·r ≤ (61/42)(M+½)`
  have hpr : (y + 1) * r ≤ (61 / 42) * (M + 1 / 2) := by nlinarith
  -- the cube of the `√ρ₊ ≤ (15/14)√ρ` comparison
  have hsp3 : sp ^ 3 ≤ (15 / 14) ^ 3 * r ^ 3 := by
    calc sp ^ 3 ≤ ((15 / 14) * r) ^ 3 := pow_le_pow_left₀ hsp0 hsp 3
      _ = (15 / 14) ^ 3 * r ^ 3 := by ring
  -- the assembled product, regrouped as `(y·r)·((y+1)·r)·r`
  have hprod : (y * r) * ((y + 1) * r) * r ≤
      ((7 / 6) * (M + 1 / 2)) * ((61 / 42) * (M + 1 / 2)) * (9 / 10) := by
    have h1 : (y * r) * ((y + 1) * r) ≤
        ((7 / 6) * (M + 1 / 2)) * ((61 / 42) * (M + 1 / 2)) :=
      mul_le_mul hyr hpr (by positivity) (by positivity)
    exact mul_le_mul h1 hr9 hr0.le (by positivity)
  calc 3 * sp ^ 3 * ((y + 1) * c * y)
      ≤ 3 * ((15 / 14) ^ 3 * r ^ 3) * ((y + 1) * M ^ 2 * y) := by
        have hcy : (y + 1) * c * y ≤ (y + 1) * M ^ 2 * y := by
          have := mul_le_mul_of_nonneg_left hcM (by positivity : (0:ℝ) ≤ y + 1)
          exact mul_le_mul_of_nonneg_right this hy0
        have hsp3' : 3 * sp ^ 3 ≤ 3 * ((15 / 14) ^ 3 * r ^ 3) := by linarith
        exact mul_le_mul hsp3' hcy (by positivity) (by positivity)
    _ = 3 * (15 / 14) ^ 3 * M ^ 2 * ((y * r) * ((y + 1) * r) * r) := by ring
    _ ≤ 3 * (15 / 14) ^ 3 * M ^ 2 *
          (((7 / 6) * (M + 1 / 2)) * ((61 / 42) * (M + 1 / 2)) * (9 / 10)) := by
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (3 * (15 / 14) ^ 3 * (7 / 6) * (61 / 42) * (9 / 10)) *
          (M ^ 2 * (M + 1 / 2) ^ 2) := by ring
    _ ≤ 6 * (M ^ 2 * (M + 1 / 2) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ 2 * (M + 1 / 2) ^ 5 := by
        have hcube : 6 * M ^ 2 ≤ 2 * (M + 1 / 2) ^ 3 := by nlinarith
        have h := mul_le_mul_of_nonneg_right hcube (sq_nonneg (M + 1 / 2))
        calc 6 * (M ^ 2 * (M + 1 / 2) ^ 2)
            = 6 * M ^ 2 * (M + 1 / 2) ^ 2 := by ring
          _ ≤ 2 * (M + 1 / 2) ^ 3 * (M + 1 / 2) ^ 2 := h
          _ = 2 * (M + 1 / 2) ^ 5 := by ring

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The graded budget fits the `ℓ`-budget**: with `DY := gs_degree_bound k n m/(k−1)`
and `|cI| := |constraintIndices m|`, `(DY+1)·|cI|·DY ≤ 2(M+½)⁵/(3ρ₊^{3/2})` whenever
`k ≥ 7`, `k+1 ≤ n`, `√(k/n) ≤ 9/10`, and `m` is the Johnson multiplicity `hab25M`. -/
theorem graded_budget_le_ell_budget {n k m : ℕ} (η : ℝ≥0)
    (hk7 : 7 ≤ k) (hkn : k + 1 ≤ n)
    (hρ : Real.sqrt ((k : ℝ) / (n : ℝ)) ≤ 9 / 10)
    (hmM : (m : ℝ) = hab25M n k η) :
    (((gs_degree_bound k n m / (k - 1) + 1) *
        (GuruswamiSudan.constraintIndices m).card *
        (gs_degree_bound k n m / (k - 1)) : ℕ) : ℝ) ≤
      2 * (hab25M n k η + 1 / 2) ^ 5 /
        (3 * hab25RhoPlus n k ^ ((3 : ℝ) / 2)) := by
  have hn0 : 0 < n := by omega
  have hk0 : 0 < k := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  set DY : ℕ := gs_degree_bound k n m / (k - 1) with hDY
  set y : ℝ := (DY : ℝ) with hy
  set c : ℝ := ((GuruswamiSudan.constraintIndices m).card : ℝ) with hc
  set r : ℝ := Real.sqrt ((k : ℝ) / (n : ℝ)) with hr
  set ρp : ℝ := hab25RhoPlus n k with hρp
  set sp : ℝ := Real.sqrt ρp with hsp
  set M : ℝ := hab25M n k η with hM
  have hρ0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = (k : ℝ) / (n : ℝ) := Real.sq_sqrt hρ0
  have hρp0 : 0 < ρp := hab25RhoPlus_pos hn0 k
  have hsp0 : 0 ≤ sp := Real.sqrt_nonneg _
  have hM3 : (3 : ℝ) ≤ M := hab25M_ge_three n k η
  -- (i) the fold-degree bound `y·r ≤ (7/6)(M+½)`
  have hDmul : (DY : ℝ) * ((k : ℝ) - 1) ≤ (gs_degree_bound k n m : ℝ) := by
    have h := Nat.div_mul_le_self (gs_degree_bound k n m) (k - 1)
    have hcast : ((DY * (k - 1) : ℕ) : ℝ) ≤ (gs_degree_bound k n m : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k)] at hcast
    simpa using hcast
  have hDle : (gs_degree_bound k n m : ℝ) ≤ ((m : ℝ) + 1 / 2) * r * n := by
    unfold gs_degree_bound
    refine le_trans (Nat.floor_le (by positivity)) (le_of_eq ?_)
    have hq : ((((k : ℚ) / (n : ℚ) : ℚ)) : ℝ) = (k : ℝ) / (n : ℝ) := by push_cast; ring
    rw [hq, hr]
  have hyr : y * r ≤ (7 / 6) * (M + 1 / 2) := by
    have hk1R : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
      linarith
    have h1 : y * ((k : ℝ) - 1) * r ≤ (((m : ℝ) + 1 / 2) * r * n) * r := by
      refine mul_le_mul_of_nonneg_right (le_trans hDmul hDle) hr0.le
    have hrr : r * r = (k : ℝ) / (n : ℝ) := by
      have h := hr2
      rw [pow_two] at h
      exact h
    have h2 : (((m : ℝ) + 1 / 2) * r * n) * r = ((m : ℝ) + 1 / 2) * (k : ℝ) := by
      calc (((m : ℝ) + 1 / 2) * r * n) * r
          = ((m : ℝ) + 1 / 2) * n * (r * r) := by ring
        _ = ((m : ℝ) + 1 / 2) * n * ((k : ℝ) / (n : ℝ)) := by rw [hrr]
        _ = ((m : ℝ) + 1 / 2) * (k : ℝ) := by field_simp
    have h3 : 6 * (k : ℝ) ≤ 7 * ((k : ℝ) - 1) := by
      have : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk7
      linarith
    have h4 : y * ((k : ℝ) - 1) * r ≤ ((m : ℝ) + 1 / 2) * (k : ℝ) := by
      rw [← h2]; exact h1
    have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
    rw [hmM] at h4
    nlinarith [mul_nonneg hy0 hr0.le,
      mul_pos hk1R (show (0 : ℝ) < M + 1 / 2 by linarith)]
  -- (ii) `r ≤ (2/7)(M+½)`
  have hrM : r ≤ (2 / 7) * (M + 1 / 2) := by
    have : (2 / 7 : ℝ) * (M + 1 / 2) ≥ 1 := by nlinarith
    linarith
  -- (iii) `sp ≤ (15/14)·r` from `ρ₊ ≤ (225/196)·ρ` at `k ≥ 7`
  have hspr : sp ≤ (15 / 14) * r := by
    have hρple : ρp ≤ (225 / 196) * ((k : ℝ) / (n : ℝ)) := by
      rw [hρp]
      unfold hab25RhoPlus
      rw [← add_div, ← mul_div_assoc]
      have h7 : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk7
      gcongr
      linarith
    have h1 : sp ≤ Real.sqrt ((225 / 196) * ((k : ℝ) / (n : ℝ))) :=
      Real.sqrt_le_sqrt hρple
    have h2 : Real.sqrt ((225 / 196) * ((k : ℝ) / (n : ℝ))) = (15 / 14) * r := by
      rw [show (225 / 196 : ℝ) = (15 / 14) ^ 2 by norm_num,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h2] at h1
    exact h1
  -- (iv) `c ≤ M²`
  have hcM : c ≤ M ^ 2 := by
    have h1 : c ≤ ((m : ℝ)) * ((m : ℝ)) := by
      rw [hc]
      exact_mod_cast constraintIndices_card_le m
    rw [hmM] at h1
    nlinarith
  -- the core, then divide
  have hcore := graded_budget_core (Nat.cast_nonneg DY) (Nat.cast_nonneg _)
    hr0 hsp0 hM3 hcM hρ hyr hrM hspr
  have hsppos : (0 : ℝ) < sp := Real.sqrt_pos.mpr hρp0
  have hcast : (((DY + 1) * (GuruswamiSudan.constraintIndices m).card * DY : ℕ) : ℝ) =
      (y + 1) * c * y := by push_cast; ring
  rw [hcast, rpow_three_halves_eq_sqrt_cube hρp0.le]
  rw [le_div_iff₀ (mul_pos (by norm_num) (pow_pos hsppos 3))]
  calc (y + 1) * c * y * (3 * sp ^ 3)
      = 3 * sp ^ 3 * ((y + 1) * c * y) := by ring
    _ ≤ 2 * (M + 1 / 2) ^ 5 := hcore

/-- **The `hNdiv` comparison at the graded budget, proven outright** — the exact shape
consumed by `johnsonNumericBound_of_K4_graded`. -/
theorem graded_budget_div_le_johnsonBoundReal {n k m : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (η δ : ℝ≥0)
    (hk7 : 7 ≤ k) (hkn : k + 1 ≤ n)
    (hρ : Real.sqrt ((k : ℝ) / (n : ℝ)) ≤ 9 / 10)
    (hmM : (m : ℝ) = hab25M n k η) :
    (((gs_degree_bound k n m / (k - 1) + 1) *
        (n * (GuruswamiSudan.constraintIndices m).card *
          (gs_degree_bound k n m / (k - 1))) : ℕ) : ℝ) /
      (Fintype.card F₀ : ℝ) ≤ johnsonBoundReal domain k η δ := by
  have hcardn : Fintype.card (Fin n) = n := Fintype.card_fin n
  set DY : ℕ := gs_degree_bound k n m / (k - 1) with hDY
  have hL := graded_budget_le_ell_budget (n := n) (k := k) (m := m) η hk7 hkn hρ hmM
  have h := nat_mul_card_div_le_johnsonBoundReal (ι₀ := Fin n) domain k η δ
    ((DY + 1) * (GuruswamiSudan.constraintIndices m).card * DY)
    (by rw [hcardn]; exact hL)
  have hshape : (DY + 1) * (GuruswamiSudan.constraintIndices m).card * DY *
      Fintype.card (Fin n) =
      (DY + 1) * (n * (GuruswamiSudan.constraintIndices m).card * DY) := by
    rw [hcardn]; ring
  rwa [hshape] at h

/-- **The closed beyond-window capstone: K4 alone ⟹ `JohnsonNumericBound`.** No numeric
side condition remains — only K4 (the BCIKS20 Steps 5–7 capture, proven on the
unique-decoding window) and the structural hypotheses. -/
theorem johnsonNumericBound_of_K4_graded_closed {n k m : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (η δ : ℝ≥0)
    (hk7 : 7 ≤ k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hρ : Real.sqrt ((k : ℝ) / (n : ℝ)) ≤ 9 / 10)
    (hmM : (m : ℝ) = hab25M n k η)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hK4 : ∀ (u : WordStack F₀ (Fin 2) (Fin n)) (E : Finset F₀) (P : F₀ → F₀[X])
      (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ n * (GuruswamiSudan.constraintIndices m).card *
        (gs_degree_bound k n m / (k - 1))) :
    JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_K4_graded domain η δ
    (n * (GuruswamiSudan.constraintIndices m).card * (gs_degree_bound k n m / (k - 1)))
    (by omega) hkn hm hδ1 hδJ le_rfl hK4
    (graded_budget_div_le_johnsonBoundReal domain η δ hk7 hkn hρ hmM)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms rpow_three_halves_eq_sqrt_cube
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms graded_budget_core
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms graded_budget_le_ell_budget
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms graded_budget_div_le_johnsonBoundReal
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms johnsonNumericBound_of_K4_graded_closed
