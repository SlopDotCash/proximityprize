/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic cube-root increment bounds for the HBK cap

The coefficient-4 majorization cap uses increments of `t^(2/3)`.  Rather than invoke derivatives
or integration, write three consecutive cube roots as `a,b,c`, so

`a^3 = b^3 + 1` and `b^3 = c^3 + 1`.

Factoring differences of cubes gives the local telescoping estimate

`9 (a^2-b^2)^2 ≤ 12 (b-c)`.

Summing this inequality makes every interior term telescope in the cube-root variable.  This is the
exact discrete analytic brick behind the target in G120. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds

/-- The real cube root of a natural number, defined by `rpow`. -/
noncomputable def natCubeRoot (i : ℕ) : ℝ := (i : ℝ) ^ ((3 : ℝ)⁻¹)

@[simp] theorem natCubeRoot_zero : natCubeRoot 0 = 0 := by
  simp [natCubeRoot]

@[simp] theorem natCubeRoot_one : natCubeRoot 1 = 1 := by
  simp [natCubeRoot]

theorem natCubeRoot_monotone : Monotone natCubeRoot := by
  intro i j hij
  apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hij)
  positivity

theorem natCubeRoot_cube (i : ℕ) : natCubeRoot i ^ 3 = i := by
  simp only [natCubeRoot]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ i)]
  norm_num

theorem natCubeRoot_sq_eq_rpow_two_thirds (i : ℕ) :
    natCubeRoot i ^ 2 = (i : ℝ) ^ ((2 : ℝ) / 3) := by
  simp only [natCubeRoot]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ i)]
  congr 1
  norm_num

/-- Consecutive increments of `t^(2/3)` decrease. -/
theorem natCubeRoot_sq_increment_antitone (i : ℕ) :
    natCubeRoot (i + 2) ^ 2 - natCubeRoot (i + 1) ^ 2 ≤
      natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2 := by
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ ((2 : ℝ) / 3)) :=
    Real.concaveOn_rpow (by norm_num) (by norm_num)
  have hs := hconc.slope_anti_adjacent
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ i))
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ (i + 2 : ℕ)))
    (show (i : ℝ) < (i + 1 : ℕ) by exact_mod_cast Nat.lt_succ_self i)
    (show ((i + 1 : ℕ) : ℝ) < (i + 2 : ℕ) by exact_mod_cast Nat.lt_succ_self (i + 1))
  rw [← natCubeRoot_sq_eq_rpow_two_thirds,
    ← natCubeRoot_sq_eq_rpow_two_thirds,
    ← natCubeRoot_sq_eq_rpow_two_thirds] at hs
  norm_num at hs ⊢
  exact hs

/-- The square increment of consecutive `2/3` powers is controlled by the preceding `1/3`
increment.  The proof is purely polynomial algebra. -/
theorem nine_mul_sq_sq_sub_sq_le_twelve_mul_sub
    {a b c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (hab : a ^ 3 = b ^ 3 + 1) (hbc : b ^ 3 = c ^ 3 + 1) :
    9 * (a ^ 2 - b ^ 2) ^ 2 ≤ 12 * (b - c) := by
  have hb : 0 ≤ b := hc.trans hcb
  have ha : 0 ≤ a := hb.trans hba
  have hdab : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
  have hdbc : 0 ≤ b - c := sub_nonneg.mpr hcb
  have hfactorAB : (a - b) * (a ^ 2 + a * b + b ^ 2) = 1 := by
    nlinarith
  have hfactorBC : (b - c) * (b ^ 2 + b * c + c ^ 2) = 1 := by
    nlinarith
  have hfirst : 3 * b * (a ^ 2 - b ^ 2) ≤ 2 := by
    have hnonneg : 0 ≤ (a - b) * (2 * a + b) :=
      mul_nonneg (sub_nonneg.mpr hba) (by positivity)
    nlinarith
  have hfirstNonneg : 0 ≤ 3 * b * (a ^ 2 - b ^ 2) := by positivity
  have hfirstSq : 9 * b ^ 2 * (a ^ 2 - b ^ 2) ^ 2 ≤ 4 := by
    have hs := (sq_le_sq₀ hfirstNonneg (by norm_num : (0 : ℝ) ≤ 2)).2 hfirst
    nlinarith
  have hsecond : 1 ≤ 3 * b ^ 2 * (b - c) := by
    have hcmp : b ^ 2 + b * c + c ^ 2 ≤ 3 * b ^ 2 := by
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hcb), sq_nonneg (b - c)]
    nlinarith [mul_nonneg hdbc (sub_nonneg.mpr hcmp)]
  have hlower :
      9 * (a ^ 2 - b ^ 2) ^ 2 ≤
        27 * b ^ 2 * (b - c) * (a ^ 2 - b ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (a ^ 2 - b ^ 2)) (sub_nonneg.mpr hsecond)]
  have hupper :
      27 * b ^ 2 * (b - c) * (a ^ 2 - b ^ 2) ^ 2 ≤ 12 * (b - c) := by
    nlinarith [mul_nonneg hdbc (sub_nonneg.mpr hfirstSq)]
  exact hlower.trans hupper

/-- The first `2/3`-power increment, from cube root `0` to cube root `1`, contributes exactly one
before the coefficient-4 scaling. -/
theorem first_increment_sq : (((1 : ℝ) ^ 2 - 0 ^ 2) ^ 2) = 1 := by norm_num

/-- **Telescoped cap-increment bound.**  For an increasing real sequence whose cubes are the
successive natural numbers, the squared `2/3`-power increments satisfy the exact finite envelope
`9 Σ Δ² ≤ 9 + 12 u_{N-1}`. -/
theorem nine_mul_sum_sq_increment_le
    (u : ℕ → ℝ) (hu0 : u 0 = 0) (hu1 : u 1 = 1) (huMono : Monotone u)
    (hstep : ∀ i, u (i + 1) ^ 3 = u i ^ 3 + 1) (N : ℕ) (hN : 0 < N) :
    9 * (∑ i ∈ Finset.range N, (u (i + 1) ^ 2 - u i ^ 2) ^ 2) ≤
      9 + 12 * u (N - 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
      obtain rfl | k := N
      · simp [hu0, hu1]
      · rw [Finset.sum_range_succ]
        have hih := ih (by omega)
        have huk : 0 ≤ u k := by
          calc
            0 = u 0 := hu0.symm
            _ ≤ u k := huMono (Nat.zero_le k)
        have hlocal := nine_mul_sq_sq_sub_sq_le_twelve_mul_sub
          huk
          (huMono (Nat.le_succ k)) (huMono (Nat.le_succ (k + 1)))
          (hstep (k + 1)) (hstep k)
        simp only [Nat.add_sub_cancel] at hih ⊢
        simp only [Nat.succ_eq_add_one] at hlocal
        nlinarith

/-- Concrete specialization to ordinary real cube roots of natural numbers. -/
theorem nine_mul_sum_natCubeRoot_sq_increment_le (N : ℕ) (hN : 0 < N) :
    9 * (∑ i ∈ Finset.range N,
      (natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2) ^ 2) ≤
      9 + 12 * natCubeRoot (N - 1) := by
  apply nine_mul_sum_sq_increment_le natCubeRoot natCubeRoot_zero natCubeRoot_one
    natCubeRoot_monotone
  · intro i
    rw [natCubeRoot_cube, natCubeRoot_cube]
    norm_num
  · exact hN

/-- The terminal cube root at the exact production saturation index is at most `16`. -/
theorem production_terminal_cubeRoot_le : natCubeRoot (4096 - 1) ≤ 16 := by
  calc
    natCubeRoot (4096 - 1) ≤ natCubeRoot 4096 := natCubeRoot_monotone (by omega)
    _ ≤ 16 := by
      change (4096 : ℝ) ^ ((3 : ℝ)⁻¹) ≤ 16
      rw [Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
      norm_num

/-- **Fully scaled production cap budget.**  The coefficient-4 cap saturates after `4096`
increments. Its squared increments satisfy exactly the relaxed G120 target (after multiplying that
target by three): `9 Σ c_i² ≤ 3216·2^40`. -/
theorem production_nine_mul_scaled_cap_sq_sum_le :
    9 * (∑ i ∈ Finset.range 4096,
      ((4 * 2 ^ 20 : ℝ) *
        (natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2)) ^ 2) ≤
      3216 * 2 ^ 40 := by
  have hsum := nine_mul_sum_natCubeRoot_sq_increment_le 4096 (by norm_num)
  have hterminal := production_terminal_cubeRoot_le
  have hraw :
      9 * (∑ i ∈ Finset.range 4096,
        (natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2) ^ 2) ≤ 201 := by
    nlinarith
  calc
    9 * (∑ i ∈ Finset.range 4096,
        ((4 * 2 ^ 20 : ℝ) *
          (natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2)) ^ 2) =
        (16 * 2 ^ 40 : ℝ) *
          (9 * ∑ i ∈ Finset.range 4096,
            (natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2) ^ 2) := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      ring
    _ ≤ (16 * 2 ^ 40 : ℝ) * 201 := by gcongr
    _ = 3216 * 2 ^ 40 := by ring

/-- The explicit zero-padded production cap increment sequence. -/
noncomputable def productionCapIncrement (i : ℕ) : ℝ :=
  if i < 4096 then
    (4 * 2 ^ 20 : ℝ) * (natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2)
  else 0

theorem productionCapIncrement_nonneg (i : ℕ) : 0 ≤ productionCapIncrement i := by
  simp only [productionCapIncrement]
  split_ifs
  · have := natCubeRoot_monotone (Nat.le_succ i)
    have hi0 : 0 ≤ natCubeRoot i := by
      simp [natCubeRoot]
      positivity
    nlinarith [sq_nonneg (natCubeRoot (i + 1) - natCubeRoot i)]
  · exact le_rfl

/-- The production cap increments decrease, including across the zero-padding boundary. -/
theorem productionCapIncrement_antitone_succ (i : ℕ) :
    productionCapIncrement (i + 1) ≤ productionCapIncrement i := by
  by_cases hi : i + 1 < 4096
  · have hi' : i < 4096 := by omega
    simp only [productionCapIncrement, if_pos hi, if_pos hi']
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [add_assoc] using natCubeRoot_sq_increment_antitone i
  · have hz : productionCapIncrement (i + 1) = 0 := by
      simp [productionCapIncrement, hi]
    rw [hz]
    exact productionCapIncrement_nonneg i

@[simp] theorem productionCapIncrement_boundary : productionCapIncrement 4096 = 0 := by
  simp [productionCapIncrement]

/-- Prefixes of the cap telescope exactly. -/
theorem sum_productionCapIncrement
    {N : ℕ} (hN : N ≤ 4096) :
    ∑ i ∈ Finset.range N, productionCapIncrement i =
      (4 * 2 ^ 20 : ℝ) * natCubeRoot N ^ 2 := by
  induction N with
  | zero => simp [productionCapIncrement]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      have hlt : N < 4096 := by omega
      simp only [productionCapIncrement, if_pos hlt]
      ring

theorem natCubeRoot_4096 : natCubeRoot 4096 = 16 := by
  apply le_antisymm
  · change (4096 : ℝ) ^ ((3 : ℝ)⁻¹) ≤ 16
    rw [Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · change 16 ≤ (4096 : ℝ) ^ ((3 : ℝ)⁻¹)
    rw [Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num

/-- The cap has total mass exactly `h=2^30` at the saturation index. -/
theorem sum_productionCapIncrement_full :
    ∑ i ∈ Finset.range 4096, productionCapIncrement i = 2 ^ 30 := by
  rw [sum_productionCapIncrement (le_refl 4096), natCubeRoot_4096]
  norm_num

/-- Extending the cap past saturation preserves its total mass, since all later increments vanish. -/
theorem sum_productionCapIncrement_eq_full_of_ge
    {N : ℕ} (hN : 4096 ≤ N) :
    ∑ i ∈ Finset.range N, productionCapIncrement i = 2 ^ 30 := by
  rw [← sum_productionCapIncrement_full]
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro i hiN hi
  have hi4096 : 4096 ≤ i := by
    by_contra h
    exact hi (Finset.mem_range.mpr (by omega))
  simp [productionCapIncrement, show ¬i < 4096 by omega]

/-- The zero-padded cap itself satisfies the exact G120 squared-mass target. -/
theorem productionCapIncrement_sq_budget :
    9 * (∑ i ∈ Finset.range 4096, productionCapIncrement i ^ 2) ≤
      3216 * 2 ^ 40 := by
  have heq :
      (∑ i ∈ Finset.range 4096, productionCapIncrement i ^ 2) =
        ∑ i ∈ Finset.range 4096,
          ((4 * 2 ^ 20 : ℝ) *
            (natCubeRoot (i + 1) ^ 2 - natCubeRoot i ^ 2)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [productionCapIncrement, if_pos (Finset.mem_range.mp hi)]
  rw [heq]
  exact production_nine_mul_scaled_cap_sq_sum_le

/-- Extending the cap beyond its saturation index adds only zeros. -/
theorem sum_productionCapIncrement_sq_eq_of_ge
    {N : ℕ} (hN : 4096 ≤ N) :
    ∑ i ∈ Finset.range N, productionCapIncrement i ^ 2 =
      ∑ i ∈ Finset.range 4096, productionCapIncrement i ^ 2 := by
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro i hiN hi
  have hi4096 : 4096 ≤ i := by
    by_contra h
    exact hi (Finset.mem_range.mpr (by omega))
  simp [productionCapIncrement, show ¬i < 4096 by omega]

end ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds

#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.nine_mul_sq_sq_sub_sq_le_twelve_mul_sub
#print axioms ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.first_increment_sq
#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.nine_mul_sum_sq_increment_le
#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.nine_mul_sum_natCubeRoot_sq_increment_le
#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.production_nine_mul_scaled_cap_sq_sum_le
#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.productionCapIncrement_antitone_succ
#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.sum_productionCapIncrement_full
#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.sum_productionCapIncrement_eq_full_of_ge
#print axioms
  ArkLib.ProximityGap.Frontier.HBKCubeRootIncrementBounds.productionCapIncrement_sq_budget
