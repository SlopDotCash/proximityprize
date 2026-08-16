/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# G117: floor-safe integer parameters for the effective HBK lane

The continuous optimizer suggests `B^3 = 2hT`, `A = h/B`, and `D = A`.  Exact integer
feasibility needs a strict inequality.  The robust choice is instead

`B = ceil((2hT)^(1/3)), A = floor(h/B), D = A-1`.

This file isolates the elementary arithmetic.  The ceiling condition `2hT ≤ B^3` implies
`2AT ≤ B^2`; losing one unit from `D` then makes
`D(A+D)T < AB^2` strict, while `AB ≤ h` holds by division.  Thus all floor overhead is moved
to the eventual degree quotient, not the Stepanov existence/nonvanishing constraints. Issue #466.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters

/-- The division choice for the `X`-degree parameter. -/
def roundedA (h B : ℕ) : ℕ := h / B

/-- Sacrifice one unit of multiplicity to make the coefficient-count inequality strict. -/
def roundedD (h B : ℕ) : ℕ := roundedA h B - 1

/-- Ordinary ceiling cube root, expressed using Mathlib's flooring `Nat.nthRoot`. -/
def ceilCubeRoot (x : ℕ) : ℕ := Nat.nthRoot 3 x + 1

/-- Exact integer quotient coming from `D * #E ≤ A + 2hB - 1`. -/
def degreeQuotient (h A B : ℕ) : ℕ := (A + 2 * h * B - 1) / (A - 1)

/-- The defining cube ceiling.  We intentionally do not special-case perfect cubes; the extra
unit is what makes the later proof uniform and strict. -/
theorem le_ceilCubeRoot_cube (x : ℕ) : x ≤ ceilCubeRoot x ^ 3 := by
  exact (Nat.lt_pow_nthRoot_add_one (by norm_num : (3 : ℕ) ≠ 0) x).le

/-- The monomial/nonvanishing constraint is automatic for `A=floor(h/B)`. -/
theorem roundedA_mul_le (h B : ℕ) : roundedA h B * B ≤ h := by
  simpa [roundedA] using Nat.div_mul_le_self h B

/-- A cube ceiling transfers to the quadratic inequality required by the multiplicity count. -/
theorem two_roundedA_mul_le_sq
    {h T B : ℕ} (hB : 0 < B) (hcube : 2 * h * T ≤ B ^ 3) :
    2 * roundedA h B * T ≤ B ^ 2 := by
  have hAB : roundedA h B * B ≤ h := roundedA_mul_le h B
  have hscaled : (2 * roundedA h B * T) * B ≤ (B ^ 2) * B := by
    calc
      (2 * roundedA h B * T) * B = 2 * (roundedA h B * B) * T := by ring
      _ ≤ 2 * h * T := by
        simpa [mul_assoc] using
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right T hAB)
      _ ≤ B ^ 3 := hcube
      _ = (B ^ 2) * B := by ring
  exact Nat.le_of_mul_le_mul_right hscaled hB

/-- **Floor-safe strict Stepanov count.**  With `A≥2`, taking `D=A-1` turns the weak
quadratic ceiling into the strict coefficient-count inequality. -/
theorem roundedD_strict_coefficient_count
    {h T B : ℕ} (hT : 0 < T) (hA : 2 ≤ roundedA h B)
    (hquad : 2 * roundedA h B * T ≤ B ^ 2) :
    roundedD h B * (roundedA h B + roundedD h B) * T <
      roundedA h B * B ^ 2 := by
  simp only [roundedD]
  have hpos : 0 < roundedA h B := by omega
  have hfactor :
      (roundedA h B - 1) * (roundedA h B + (roundedA h B - 1)) <
        roundedA h B * (2 * roundedA h B) := by
    have hsub : roundedA h B - 1 + 1 = roundedA h B := by omega
    nlinarith
  have hstrict :
      (roundedA h B - 1) * (roundedA h B + (roundedA h B - 1)) * T <
        roundedA h B * (2 * roundedA h B * T) := by
    simpa [mul_assoc] using (Nat.mul_lt_mul_right hT).2 hfactor
  exact hstrict.trans_le (Nat.mul_le_mul_left _ hquad)

/-- Combined floor-safe parameter package from a cube ceiling. -/
theorem rounded_parameters_feasible
    {h T B : ℕ} (hT : 0 < T) (hB : 0 < B) (hA : 2 ≤ roundedA h B)
    (hcube : 2 * h * T ≤ B ^ 3) :
    roundedA h B * B ≤ h ∧
      roundedD h B * (roundedA h B + roundedD h B) * T <
        roundedA h B * B ^ 2 := by
  refine ⟨roundedA_mul_le h B, ?_⟩
  exact roundedD_strict_coefficient_count hT hA (two_roundedA_mul_le_sq hB hcube)

/-- At the production alphabet size, the ceiling cube root stays far below `h/2` for every
relevant prefix `1 ≤ T ≤ h`; hence the division parameter `A` is certainly at least two. -/
theorem production_roundedA_ge_two
    {T : ℕ} (hTle : T ≤ 2 ^ 30) :
    2 ≤ roundedA (2 ^ 30) (ceilCubeRoot (2 * (2 ^ 30) * T)) := by
  let B := ceilCubeRoot (2 * (2 ^ 30) * T)
  have hx : 2 * (2 ^ 30) * T < (2 ^ 21) ^ 3 := by
    calc
      2 * (2 ^ 30) * T ≤ 2 * (2 ^ 30) * (2 ^ 30) :=
        Nat.mul_le_mul_left _ hTle
      _ < (2 ^ 21) ^ 3 := by norm_num
  have hroot : Nat.nthRoot 3 (2 * (2 ^ 30) * T) < 2 ^ 21 :=
    (Nat.nthRoot_lt_iff (by norm_num : (3 : ℕ) ≠ 0)).2 hx
  have hBbound : B ≤ 2 ^ 21 := by
    change Nat.nthRoot 3 (2 * (2 ^ 30) * T) + 1 ≤ 2 ^ 21
    exact Nat.succ_le_iff.mpr hroot
  have hBpos : 0 < B := by simp [B, ceilCubeRoot]
  rw [roundedA]
  apply (Nat.le_div_iff_mul_le hBpos).2
  calc
    2 * B ≤ 2 * (2 ^ 21) := Nat.mul_le_mul_left 2 hBbound
    _ ≤ 2 ^ 30 := by norm_num

/-- Stronger production lower bound used to absorb the degree-quotient rounding overhead. -/
theorem production_roundedA_ge_thirtyTwo
    {T : ℕ} (hTle : T ≤ 2 ^ 30) :
    32 ≤ roundedA (2 ^ 30) (ceilCubeRoot (2 * (2 ^ 30) * T)) := by
  let B := ceilCubeRoot (2 * (2 ^ 30) * T)
  have hx : 2 * (2 ^ 30) * T < (2 ^ 21) ^ 3 := by
    calc
      2 * (2 ^ 30) * T ≤ 2 * (2 ^ 30) * (2 ^ 30) :=
        Nat.mul_le_mul_left _ hTle
      _ < (2 ^ 21) ^ 3 := by norm_num
  have hroot : Nat.nthRoot 3 (2 * (2 ^ 30) * T) < 2 ^ 21 :=
    (Nat.nthRoot_lt_iff (by norm_num : (3 : ℕ) ≠ 0)).2 hx
  have hBbound : B ≤ 2 ^ 21 := by
    change Nat.nthRoot 3 (2 * (2 ^ 30) * T) + 1 ≤ 2 ^ 21
    exact Nat.succ_le_iff.mpr hroot
  have hBpos : 0 < B := by simp [B, ceilCubeRoot]
  rw [roundedA]
  apply (Nat.le_div_iff_mul_le hBpos).2
  calc
    32 * B ≤ 32 * (2 ^ 21) := Nat.mul_le_mul_left 32 hBbound
    _ ≤ 2 ^ 30 := by norm_num

/-- Fully instantiated production floor-safe parameter package for every nonempty prefix. -/
theorem production_rounded_parameters_feasible
    {T : ℕ} (hT : 0 < T) (hTle : T ≤ 2 ^ 30) :
    let B := ceilCubeRoot (2 * (2 ^ 30) * T)
    roundedA (2 ^ 30) B * B ≤ 2 ^ 30 ∧
      roundedD (2 ^ 30) B * (roundedA (2 ^ 30) B + roundedD (2 ^ 30) B) * T <
        roundedA (2 ^ 30) B * B ^ 2 := by
  dsimp only
  apply rounded_parameters_feasible hT
  · simp [ceilCubeRoot]
  · exact production_roundedA_ge_two hTle
  · exact le_ceilCubeRoot_cube _

/-- A rational `9/4` envelope for the degree quotient.  The deliberately generous hypotheses
`A,B≥32` make all rounding overhead negligible while retaining a coefficient below the final
prefix target `4`. -/
theorem four_mul_degreeQuotient_le_nine_mul_sq
    {h A B : ℕ} (hA : 32 ≤ A) (hB : 32 ≤ B)
    (hupper : h ≤ (A + 1) * B) :
    4 * degreeQuotient h A B ≤ 9 * B ^ 2 := by
  have hD : 0 < A - 1 := by omega
  have hnum : A + 2 * h * B - 1 ≤ A + 2 * h * B := Nat.sub_le _ _
  have hmain : 4 * (A + 2 * h * B - 1) ≤ 9 * B ^ 2 * (A - 1) := by
    calc
      4 * (A + 2 * h * B - 1) ≤ 4 * (A + 2 * h * B) :=
        Nat.mul_le_mul_left 4 hnum
      _ ≤ 4 * (A + 2 * ((A + 1) * B) * B) := by
        gcongr
      _ ≤ 9 * B ^ 2 * (A - 1) := by
        have hratio : A ≤ 3 * (A - 17) := by omega
        have hBsq : 12 ≤ B ^ 2 := by nlinarith
        have hthree : 3 * (4 * A) ≤ 3 * ((A - 17) * B ^ 2) := by
          calc
            3 * (4 * A) = A * 12 := by ring
            _ ≤ (3 * (A - 17)) * 12 := Nat.mul_le_mul_right 12 hratio
            _ ≤ (3 * (A - 17)) * B ^ 2 :=
              Nat.mul_le_mul_left _ hBsq
            _ = 3 * ((A - 17) * B ^ 2) := by ring
        have haux : 4 * A ≤ (A - 17) * B ^ 2 :=
          Nat.le_of_mul_le_mul_left hthree (by norm_num)
        have hsub1 : A - 1 + 1 = A := by omega
        have hsub17 : A - 17 + 17 = A := by omega
        nlinarith
  have hquotient :
      degreeQuotient h A B * (A - 1) ≤ A + 2 * h * B - 1 := by
    exact Nat.div_mul_le_self _ _
  have hscaled :
      (4 * degreeQuotient h A B) * (A - 1) ≤ (9 * B ^ 2) * (A - 1) := by
    calc
      (4 * degreeQuotient h A B) * (A - 1) =
          4 * (degreeQuotient h A B * (A - 1)) := by ring
      _ ≤ 4 * (A + 2 * h * B - 1) := Nat.mul_le_mul_left 4 hquotient
      _ ≤ 9 * B ^ 2 * (A - 1) := hmain
      _ = (9 * B ^ 2) * (A - 1) := rfl
  exact Nat.le_of_mul_le_mul_right hscaled hD

/-- Division gives the complementary upper bracket `h < (A+1)B`. -/
theorem lt_succ_roundedA_mul
    {h B : ℕ} (hB : 0 < B) : h < (roundedA h B + 1) * B := by
  exact (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_self (roundedA h B))

/-- Production specialization of the rational `9/4` quotient envelope. -/
theorem production_four_mul_degreeQuotient_le_nine_mul_sq
    {T : ℕ} (hT : 0 < T) (hTle : T ≤ 2 ^ 30) :
    let B := ceilCubeRoot (2 * (2 ^ 30) * T)
    4 * degreeQuotient (2 ^ 30) (roundedA (2 ^ 30) B) B ≤ 9 * B ^ 2 := by
  dsimp only
  let B := ceilCubeRoot (2 * (2 ^ 30) * T)
  have hBpos : 0 < B := by simp [B, ceilCubeRoot]
  have hrootLower : 2 ^ 10 ≤ Nat.nthRoot 3 (2 * (2 ^ 30) * T) := by
    apply (Nat.le_nthRoot_iff (by norm_num : (3 : ℕ) ≠ 0)).2
    have hTone : 1 ≤ T := hT
    calc
      (2 ^ 10) ^ 3 ≤ 2 * (2 ^ 30) * 1 := by norm_num
      _ ≤ 2 * (2 ^ 30) * T := Nat.mul_le_mul_left _ hTone
  have hB32 : 32 ≤ B := by
    change 32 ≤ Nat.nthRoot 3 (2 * (2 ^ 30) * T) + 1
    have : 32 ≤ Nat.nthRoot 3 (2 * (2 ^ 30) * T) :=
      (by norm_num : 32 ≤ 2 ^ 10).trans hrootLower
    omega
  apply four_mul_degreeQuotient_le_nine_mul_sq
  · exact production_roundedA_ge_thirtyTwo hTle
  · exact hB32
  · exact (lt_succ_roundedA_mul hBpos).le

/-- **Uniform normalized prefix coefficient `4`.** Cubing the `9/4` quotient envelope and
paying the exact ceiling-root overhead still fits below `4 (hT)^(2/3)`, expressed without real
roots as `Q^3 ≤ 64(hT)^2`. -/
theorem production_degreeQuotient_cube_le
    {T : ℕ} (hT : 0 < T) (hTle : T ≤ 2 ^ 30) :
    let B := ceilCubeRoot (2 * (2 ^ 30) * T)
    degreeQuotient (2 ^ 30) (roundedA (2 ^ 30) B) B ^ 3 ≤
      64 * ((2 ^ 30) * T) ^ 2 := by
  dsimp only
  let x := 2 * (2 ^ 30) * T
  let r := Nat.nthRoot 3 x
  let B := ceilCubeRoot x
  let Q := degreeQuotient (2 ^ 30) (roundedA (2 ^ 30) B) B
  have hq : 4 * Q ≤ 9 * B ^ 2 := by
    exact production_four_mul_degreeQuotient_le_nine_mul_sq hT hTle
  have hqcube : 64 * Q ^ 3 ≤ 729 * B ^ 6 := by
    have := Nat.pow_le_pow_left hq 3
    nlinarith
  have hrLower : 2 ^ 10 ≤ r := by
    apply (Nat.le_nthRoot_iff (by norm_num : (3 : ℕ) ≠ 0)).2
    have hTone : 1 ≤ T := hT
    calc
      (2 ^ 10) ^ 3 ≤ 2 * (2 ^ 30) * 1 := by norm_num
      _ ≤ 2 * (2 ^ 30) * T := Nat.mul_le_mul_left _ hTone
  have hBformula : B = r + 1 := by rfl
  have hBscale : 1024 * B ≤ 1025 * r := by
    rw [hBformula]
    nlinarith
  have hBpow : 1024 ^ 6 * B ^ 6 ≤ 1025 ^ 6 * r ^ 6 := by
    have := Nat.pow_le_pow_left hBscale 6
    nlinarith
  have hrCube : r ^ 3 ≤ x := by
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num : (3 : ℕ) ≠ 0))
  have hrSix : r ^ 6 ≤ 4 * ((2 ^ 30) * T) ^ 2 := by
    have hsquare := Nat.pow_le_pow_left hrCube 2
    dsimp [x] at hsquare
    nlinarith
  have hBfinal :
      1024 ^ 6 * B ^ 6 ≤ 1025 ^ 6 * (4 * ((2 ^ 30) * T) ^ 2) := by
    exact hBpow.trans (Nat.mul_le_mul_left _ hrSix)
  have hscaled :
      (64 * 1024 ^ 6) * Q ^ 3 ≤
        (64 * 1024 ^ 6) * (64 * ((2 ^ 30) * T) ^ 2) := by
    calc
      (64 * 1024 ^ 6) * Q ^ 3 = 1024 ^ 6 * (64 * Q ^ 3) := by ring
      _ ≤ 1024 ^ 6 * (729 * B ^ 6) := Nat.mul_le_mul_left _ hqcube
      _ = 729 * (1024 ^ 6 * B ^ 6) := by ring
      _ ≤ 729 * (1025 ^ 6 * (4 * ((2 ^ 30) * T) ^ 2)) :=
        Nat.mul_le_mul_left _ hBfinal
      _ = (729 * 1025 ^ 6 * 4) * ((2 ^ 30) * T) ^ 2 := by ring
      _ ≤ (4096 * 1024 ^ 6) * ((2 ^ 30) * T) ^ 2 := by
        exact Nat.mul_le_mul_right _ (by norm_num)
      _ = (64 * 1024 ^ 6) * (64 * ((2 ^ 30) * T) ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

end ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters

#print axioms ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.roundedA_mul_le
#print axioms ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.le_ceilCubeRoot_cube
#print axioms ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.two_roundedA_mul_le_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.roundedD_strict_coefficient_count
#print axioms
  ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.rounded_parameters_feasible
#print axioms
  ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.production_rounded_parameters_feasible
#print axioms
  ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.four_mul_degreeQuotient_le_nine_mul_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.production_four_mul_degreeQuotient_le_nine_mul_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G117HBKFloorSafeParameters.production_degreeQuotient_cube_le
