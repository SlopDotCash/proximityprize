/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterMu16Locator
import Mathlib.Data.NNReal.Basic

/-!
# Exact arithmetic for the rate-quarter scale lift over the P1 prime

The smooth domain has `N=2^30=16m`, with `m=2^26`.  Splitting the hole fibre
into three private pieces of size `r=(m-1)/3` leaves one genuinely affine hole
coordinate.  Thus the construction has `N-1` safe scalars and three unsafe
scalars, for `N+2` in total, at agreement threshold `8m+r+1`.

This file also certifies the concrete field constants used by the unsafe
scalars.  The only large computations use a proved square-and-multiply
implementation, so kernel reduction is logarithmic in the exponent.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic

open ArkLib.ProximityGap.PrizeShapePrimeP30

abbrev F := ZMod P

local instance localInstance_P1RateQuarterScaleArithmetic_1 : Fact (Nat.Prime P) := ⟨prime_P⟩

abbrev N : ℕ := 2 ^ 30
abbrev m : ℕ := 2 ^ 26
abbrev k : ℕ := 2 ^ 28
abbrev r : ℕ := (m - 1) / 3

theorem N_eq_sixteen_mul_m : N = 16 * m := by norm_num
theorem k_eq_four_mul_m : k = 4 * m := by norm_num
theorem three_mul_r_add_one : 3 * r + 1 = m := by norm_num
theorem r_pos : 0 < r := by norm_num

/-- General bookkeeping identity before maximizing the three private pieces. -/
theorem bad_count_of_three_mul_le {m0 r0 : ℕ} (h : 3 * r0 ≤ m0) :
    (15 * m0 + 3 * r0) + 3 * (m0 - 3 * r0) = 18 * m0 - 6 * r0 := by
  omega

/-- At the maximal split the scalar count is two above the domain size. -/
theorem maximal_bad_count :
    (15 * m + 3 * r) + 3 * (m - 3 * r) = N + 2 := by norm_num

/-- The agreement threshold supplied by an enlarged core and one fresh point. -/
abbrev threshold : ℕ := 8 * m + r + 1

/-- The resulting strongest radius from this isolated-fibre construction. -/
noncomputable abbrev delta : ℝ≥0 := (23 * m - 2 : ℕ) / (48 * m : ℕ)

theorem delta_eq_twentyThree_over_fortyEight_correction :
    delta = (23 / 48 : ℝ≥0) - 2 / (3 * N : ℕ) := by
  have hle : (2 / (3 * N : ℕ) : ℝ≥0) ≤ 23 / 48 := by
    norm_num [N]
    rw [div_le_div_iff₀] <;> norm_num
  apply NNReal.coe_injective
  rw [NNReal.coe_sub hle]
  push_cast
  norm_num [delta, N, m]

theorem delta_lt_half : delta < (1 / 2 : ℝ≥0) := by
  norm_num [delta, m]

theorem agreement_mass_eq_threshold :
    (1 - delta) * (N : ℝ≥0) = threshold := by
  have hd : delta ≤ 1 := le_of_lt delta_lt_half |>.trans (by norm_num)
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub hd]
  push_cast
  norm_num [delta, threshold, N, m, r]

/-! ## Kernel-cheap exact field certificates -/

private def binaryPowAux {M : Type*} [Monoid M] (a : M) (n : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then
        binaryPowAux (a * a) (n / 2) fuel
      else
        a * binaryPowAux (a * a) (n / 2) fuel

private def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  binaryPowAux a n (n + 1)

private theorem binaryPowAux_eq_pow {M : Type*} [Monoid M] (a : M) (n fuel : ℕ)
    (hnfuel : n < fuel) : binaryPowAux a n fuel = a ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [binaryPowAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n := by
  exact binaryPowAux_eq_pow a n (n + 1) (by omega)

/-- `z=g^m`, the primitive sixteenth-root quotient coordinate. -/
abbrev z : F :=
  357111556877444407914257742635116754287240874648

/-- The quotient coordinate of the isolated residue-15 fibre. -/
abbrev y : F :=
  52837943853059877610349754974223641325891505919

/-- The universal locator-line parameter at the concrete root `z`. -/
abbrev lambdaValue : F :=
  99794237287072257623133553212334614220838842719

theorem g_pow_m : g ^ m = z := by
  rw [← binaryPow_eq_pow]
  decide

theorem z_pow_eight : z ^ 8 = (-1 : F) := by decide
theorem z_pow_fifteen : z ^ 15 = y := by decide

theorem lambdaValue_eq_locatorLambda :
    lambdaValue =
      HalfPredecessorRateQuarterMu16Locator.locatorLambda z := by
  decide

/-- Values of the three line directions on the isolated hole fibre. -/
def holeValue : Fin 3 → F := ![
  0,
  347297579018425152216873519749516351364382315364,
  334882322071681334791617893574014967121315340569]

/-- Unsafe scalar multipliers for the affine hole row `(x,2)`. -/
def unsafeConstant : Fin 3 → F := ![
  182687704666362864775460604089535377560070782976,
  298187650492982251514051561464409169503357575630,
  163666833025787997478869914264350754475332111189]

theorem holeValue_ne_two (i : Fin 3) : holeValue i ≠ (2 : F) := by
  fin_cases i <;> decide

theorem holeValue_pairwise_ne : Function.Injective holeValue := by decide

theorem unsafeConstant_formula (i : Fin 3) :
    unsafeConstant i = (holeValue i - 1) / (2 - holeValue i) := by
  have hden : (2 : F) - holeValue i ≠ 0 := sub_ne_zero.mpr (holeValue_ne_two i).symm
  apply (eq_div_iff hden).2
  fin_cases i <;> decide

theorem unsafeConstant_injective : Function.Injective unsafeConstant := by decide

/-- None of the three unsafe multipliers lies in the smooth subgroup.  This
is precisely the condition separating all unsafe scalars from all safe
scalars. -/
theorem unsafeConstant_pow_N_ne_one (i : Fin 3) :
    unsafeConstant i ^ N ≠ (1 : F) := by
  fin_cases i <;> rw [← binaryPow_eq_pow] <;> decide

end ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
#print axioms maximal_bad_count
#print axioms agreement_mass_eq_threshold
#print axioms g_pow_m
#print axioms unsafeConstant_pow_N_ne_one
