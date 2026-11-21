/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Research.ProximityGap.Frontier.SmoothDeepMcaThreshold
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-! # Separation of worst-center list and line-MCA security

At exactly k+1 agreements, distinct interleaved list members have disjoint
families of k-subsets. In fields of order at least choose(n,k+1) squared, the
worst MCA numerator attains choose(n,k+1). Hence the ratio between this
numerator and even the packing upper bound for a list is at least n-k.
-/

namespace ProximityGap.BoundaryListMcaSeparation

open Code
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- The finite packing ratio, allowing the floor in the worst-center list cap. -/
theorem packing_ratio (n k : ℕ) :
    (n.choose k / (k+1)) * (n-k) ≤ n.choose (k+1) := by
  apply Nat.le_of_mul_le_mul_right (c := k+1) _ (Nat.succ_pos k)
  rw [Nat.choose_succ_right_eq]
  calc (n.choose k / (k+1)) * (n-k) * (k+1) =
      (n.choose k / (k+1) * (k+1)) * (n-k) := by ac_rfl
    _ ≤ n.choose k * (n-k) :=
      Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)

omit [DecidableEq F] in
/-- A worst-center list upper and the exact line-MCA error at the same grid
point on the same supplied domain. -/
theorem boundary (D : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (hfield : (n.choose (k+1))^2 ≤ Fintype.card F) (m : ℕ) :
    Lambda (ListInterpolationBoundary.words D k m) (((n-(k+1) : ℕ) : ℝ)/n) ≤
      (n.choose k / (k+1) : ℕ) ∧
    epsMCA (F := F) (ReedSolomon.code D k : Set (Fin n → F))
      (((n-(k+1) : ℕ) : ℝ≥0)/n) = (n.choose (k+1) : ℝ≥0∞) / Fintype.card F := by
  have hle : k+1 ≤ n := hkn
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast NeZero.pos n
  have he : (1-(((n-(k+1) : ℕ) : ℝ≥0)/n)) * (Fintype.card (Fin n) : ℝ≥0) =
      (k+1 : ℕ) := by
    rw [Fintype.card_fin, tsub_mul, one_mul, div_mul_cancel₀ _ hn.ne']
    exact_mod_cast Nat.sub_sub_self hle
  constructor
  · have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D k (k+1) m
      (((n-(k+1) : ℕ) : ℝ)/n) (Nat.le_succ k) (by
        rw [Fintype.card_fin, div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne n)),
          Nat.cast_sub hle]
        linarith)
    simpa only [Fintype.card_fin, Nat.choose_succ_self_right] using hu
  · rw [← BoundarySecurityBudget.rsCode_eq_code]
    exact Ownership.epsMCA_eq_boundary_choose_of_genericFar D hk
      (he ▸ by exact_mod_cast Nat.lt_succ_self k) he.le hfield

/-- At rate one eighth and length 64 the 128-bit list test passes at every
positive width while the scalar MCA test already fails at 55 errors. -/
def Separated64 (D : Fin 64 ↪ F) : Prop :=
  (∀ m, Lambda (ListInterpolationBoundary.words D 8 m) (55/64) ≤
    (Fintype.card F / 2^128 : ℕ)) ∧
  epsMCA (F := F) (ReedSolomon.code D 8 : Set (Fin 64 → F)) (55/64) =
    27540584512 / (Fintype.card F : ℝ≥0∞) ∧
  1 / (2^128 : ℝ≥0∞) < epsMCA (F := F) (ReedSolomon.code D 8 : Set (Fin 64 → F)) (55/64)

omit [DecidableEq F] in
theorem length64 (D : Fin 64 ↪ F)
    (hfield : 27540584512^2 ≤ Fintype.card F)
    (hlo : 491796152 ≤ Fintype.card F / 2^128)
    (hhi : Fintype.card F / 2^128 < 27540584512) : Separated64 D := by
  have hc : Nat.choose 64 9 = 27540584512 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have hl : Nat.choose 64 8 / 9 = 491796152 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have hcard : (Nat.choose 64 (8+1))^2 ≤ Fintype.card F := hc ▸ hfield
  have h (m : ℕ) := boundary D (k := 8) (by decide) (by decide) hcard m
  have he : epsMCA (F := F) (ReedSolomon.code D 8 : Set (Fin 64 → F)) (55/64) =
      27540584512 / (Fintype.card F : ℝ≥0∞) := by
    simpa only [show 8+1 = 9 by decide, show 64-9 = 55 by decide, hc, Nat.cast_ofNat] using (h 0).2
  refine ⟨fun m => ?_, he, ?_⟩
  · have hu : Lambda (ListInterpolationBoundary.words D 8 m) (55/64) ≤ (491796152 : ℕ∞) := by
      simpa only [show 8+1 = 9 by decide, show 64-9 = 55 by decide, hl, Nat.cast_ofNat] using (h m).1
    exact hu.trans (by exact_mod_cast hlo)
  · rw [he]
    apply lt_of_not_ge
    intro hgood
    apply (not_le_of_gt hhi)
    exact (BoundarySecurityBudget.count_ratio_le_iff (a := 27540584512)
      (D := 2^128) Fintype.card_pos (by decide)).mp (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hgood)

/-- Nine agreements lie strictly below the finite Johnson agreement threshold. -/
theorem strictly_beyond_johnson : 9^2 < (64 : ℕ) * (8-1) := by decide

/-- The full line-MCA and worst-center list predicates have different first failure
steps at length 64 and dimension eight. -/
def Profiles64 (D : Fin 64 ↪ F) : Prop :=
  (∀ m, 0 < m → ∀ δ : ℝ, Lambda (ListInterpolationBoundary.words D 8 m) δ ≤
    (Fintype.card F / 2^128 : ℕ) ↔ δ < 56/64) ∧
  (∀ δ : ℝ≥0, epsMCA (F := F) (ReedSolomon.code D 8 : Set (Fin 64 → F)) δ ≤
    1/(2^128 : ℝ≥0∞) ↔ δ < 54/64)

set_option maxRecDepth 10000 in
/-- The exact pair of first failures holds throughout a whole interval of field orders. -/
theorem profiles64 (D : Fin 64 ↪ F) [ReedSolomon.Smooth D]
    (hlo : 612012989 ≤ Fintype.card F/2^128)
    (hhi : Fintype.card F/2^128 ≤ 2366768981) : Profiles64 D := by
  let q := Fintype.card F
  let B := q/2^128
  have hF : 612012989*2^128 ≤ q :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2^128)).mp hlo
  have hnot : ¬ (Fintype.card (Fin 64)).choose 8 ≤ B := by
    rw [Fintype.card_fin, Nat.choose_eq_descFactorial_div_factorial]
    exact not_le_of_gt (hhi.trans_lt (by decide))
  constructor
  · intro m hm δ
    have h := ListInterpolationBoundary.good_iff D (k := 8) (by decide) (by simp) hm
      (B := B) ((by rw [Fintype.card_fin, Nat.choose_eq_descFactorial_div_factorial]; decide :
        (Fintype.card (Fin 64)).choose 8/(8+1) ≤ 612012989).trans hlo)
      (Nat.div_lt_self Fintype.card_pos (by decide : 1 < 2^128)) δ
    rw [ite_eq_right hnot] at h
    simpa only [Fintype.card_fin, show 64-8=56 by decide, Nat.cast_ofNat] using h
  · intro δ
    have hratio (c : ℕ) : (c : ℝ≥0∞) / q ≤ 1/(2^128 : ℝ≥0∞) ↔ c ≤ B := by
      change (c : ℝ≥0∞) / q ≤ 1/(2^128 : ℝ≥0∞) ↔ c ≤ q/2^128
      convert (BoundarySecurityBudget.count_ratio_le_iff (a := c) (q := q) (D := 2^128)
          Fintype.card_pos (by decide)) using 2 <;> norm_num
    have h := SmoothDeepMcaThreshold.epsMCA_le_iff D (k := 8) (a := 0) (t := 10)
      (B := B) (L := B) (by decide) (by decide) (by simp)
      ((by rw [Fintype.card_fin]; simp only [Nat.choose_eq_descFactorial_div_factorial]; decide :
        (Fintype.card (Fin 64)).choose (8+1)/Nat.choose 10 8 ≤ 612012989).trans hlo)
      (by
        rw [Fintype.card_fin, pow_zero, mul_one]
        exact (Nat.mul_le_mul_left _ hhi).trans_lt
          (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide))
      (by
        have hc : (B+1).choose 2 ≤ (2366768981+1)^2 :=
          (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hhi 1) 2)
        rw [show B+1-B=1 by omega, mul_one, Fintype.card_fin]
        exact ((Nat.mul_le_mul_left 8 hc).trans_lt
          (by decide : 8*(2366768981+1)^2 < 612012989*2^128-64)).trans_le (Nat.sub_le_sub_right hF _))
      (1/(2^128 : ℝ≥0∞)) ((hratio B).mpr le_rfl)
      (lt_of_not_ge (fun he => Nat.not_succ_le_self B ((hratio (B+1)).mp he))) δ
    simpa only [Fintype.card_fin, show 64-10 = 54 by decide, Nat.cast_ofNat] using h

open ArkLib.ProximityGap
local instance : Fact (Nat.Prime PrizeShapePrimeP30.P) := ⟨PrizeShapePrimeP30.prime_P⟩
local instance : Fact (Nat.Prime PrizeShapePrimeP30Second.P) := ⟨PrizeShapePrimeP30Second.prime_P⟩

theorem first_prime (D : Fin 64 ↪ ZMod PrizeShapePrimeP30.P) : Separated64 D := by
  apply length64 <;> rw [ZMod.card] <;> decide

theorem second_prime (D : Fin 64 ↪ ZMod PrizeShapePrimeP30Second.P) : Separated64 D := by
  apply length64 <;> rw [ZMod.card] <;> decide

theorem first_prime_profiles (D : Fin 64 ↪ ZMod PrizeShapePrimeP30.P) [ReedSolomon.Smooth D] :
    Profiles64 D := by
  apply profiles64 <;> rw [ZMod.card] <;> decide

theorem second_prime_profiles (D : Fin 64 ↪ ZMod PrizeShapePrimeP30Second.P) [ReedSolomon.Smooth D] :
    Profiles64 D := by
  apply profiles64 <;> rw [ZMod.card] <;> decide

#print axioms first_prime_profiles
#print axioms second_prime_profiles
#print axioms boundary
#print axioms first_prime
#print axioms second_prime

end ProximityGap.BoundaryListMcaSeparation
