/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_16(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one deconflicted rung beyond `E_14`,
deliberately skipping the live-held `E_15` lane. It records the exact cross-polytope /
Lam--Leung polynomial at
depth `r = 16`, plus the Wick bound and strict positive cushion. This is deliberately only a
char-0 rung; it does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E16ClosedForm

/-- `E_16(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 16`, in closed form. -/
def E16 (n : ℤ) : ℤ :=
  191898783962510625 * n ^ 16
    - 23027854075501275000 * n ^ 15
    + 1334336211152657212500 * n ^ 14
    - 49245065940459476587500 * n ^ 13
    + 1287813967206919849446750 * n ^ 12
    - 25154061471558716584387500 * n ^ 11
    + 377316765521315604818583750 * n ^ 10
    - 4405584938967849802974558750 * n ^ 9
    + 40181545994755855067470617525 * n ^ 8
    - 284879023752335157898067214900 * n ^ 7
    + 1549084737597916888155144471750 * n ^ 6
    - 6307793682861004243229824890750 * n ^ 5
    + 18493758026455272509286029400165 * n ^ 4
    - 36558503677958104270087357736070 * n ^ 3
    + 43121625464306630774785353573915 * n ^ 2
    - 22558338448680631922553895942275 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_sixteen (n : ℤ) : wick 16 n = 191898783962510625 * n ^ 16 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_16(2) = 601080390 = C(32,16)`. -/
theorem E16_two : E16 2 = 601080390 := by decide

/-- `E_16(4) = 361297635242552100`. -/
theorem E16_four : E16 4 = 361297635242552100 := by decide

/-! ## The exact char-0 deficit `D_16 = wick 16 n − E_16(ℂ)` -/

/-- The exact deficit `wick 16 n − E_16(ℂ)`. Its leading nonzero coefficient is
`C(16,2)·31‼ = 23027854075501275000`. -/
theorem deficit_sixteen (n : ℤ) :
    wick 16 n - E16 n =
      23027854075501275000 * n ^ 15
        - 1334336211152657212500 * n ^ 14
        + 49245065940459476587500 * n ^ 13
        - 1287813967206919849446750 * n ^ 12
        + 25154061471558716584387500 * n ^ 11
        - 377316765521315604818583750 * n ^ 10
        + 4405584938967849802974558750 * n ^ 9
        - 40181545994755855067470617525 * n ^ 8
        + 284879023752335157898067214900 * n ^ 7
        - 1549084737597916888155144471750 * n ^ 6
        + 6307793682861004243229824890750 * n ^ 5
        - 18493758026455272509286029400165 * n ^ 4
        + 36558503677958104270087357736070 * n ^ 3
        - 43121625464306630774785353573915 * n ^ 2
        + 22558338448680631922553895942275 * n ^ 1 := by
  simp only [wick_sixteen, E16]; ring

/-- `wick 16 n − E_16 = n · (Σ_k c_k · (n-5)^k)` with all `c_k ≥ 0`. -/
theorem deficit_sixteen_factored_v (n : ℤ) :
    wick 16 n - E16 n =
      n * (        8604831201382532874932469450
        + 14022582233526125327422821285 * (n - 5) ^ 1
        + 23653560298665624058210424220 * (n - 5) ^ 2
        + 24487296934052178789102024210 * (n - 5) ^ 3
        + 10942211359114512343896700125 * (n - 5) ^ 4
        + 6054230223835569595019962125 * (n - 5) ^ 5
        + 1901429695605631464287039025 * (n - 5) ^ 6
        + 435045846827984935487919975 * (n - 5) ^ 7
        + 112655488918450579360008750 * (n - 5) ^ 8
        + 11667934210752197450572500 * (n - 5) ^ 9
        + 2282933734214251059191250 * (n - 5) ^ 10
        + 112701737908275193928250 * (n - 5) ^ 11
        + 14901580237302158400000 * (n - 5) ^ 12
        + 277613574132432037500 * (n - 5) ^ 13
        + 23027854075501275000 * (n - 5) ^ 14) := by
  rw [deficit_sixteen]; ring_nf

/-- `0 ≤ wick 16 n − E16 n` for `n ≥ 5`, from the nonnegative `v = n−5` certificate. -/
theorem deficit_sixteen_nonneg_from_five (n : ℤ) (hn : 5 ≤ n) :
    0 ≤ wick 16 n - E16 n := by
  have hu0 : (0 : ℤ) ≤ n - 5 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_sixteen_factored_v]
  have h0 : (0 : ℤ) ≤ n * 8604831201382532874932469450 := by positivity
  have h1 : (0 : ℤ) ≤ n * (14022582233526125327422821285 * (n - 5) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (23653560298665624058210424220 * (n - 5) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (24487296934052178789102024210 * (n - 5) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (10942211359114512343896700125 * (n - 5) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (6054230223835569595019962125 * (n - 5) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (1901429695605631464287039025 * (n - 5) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (435045846827984935487919975 * (n - 5) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (112655488918450579360008750 * (n - 5) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (11667934210752197450572500 * (n - 5) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (2282933734214251059191250 * (n - 5) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (112701737908275193928250 * (n - 5) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (14901580237302158400000 * (n - 5) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (277613574132432037500 * (n - 5) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (23027854075501275000 * (n - 5) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

/-- Base case `n=2`. -/
theorem E16_le_wick_base_two : E16 2 ≤ wick 16 2 := by rw [E16_two, wick_sixteen]; norm_num

/-- Base case `n=4`. -/
theorem E16_le_wick_base_four : E16 4 ≤ wick 16 4 := by rw [E16_four, wick_sixteen]; norm_num

/-- The depth-16 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2` or
`n ≥ 4`. The shifted positivity certificate starts at `n = 5`, so `n = 4` is kept as an
explicit dyadic base case. -/
theorem E16_le_wick (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : E16 n ≤ wick 16 n := by
  rcases hn with rfl | hge
  · exact E16_le_wick_base_two
  · by_cases h4 : n = 4
    · subst n
      exact E16_le_wick_base_four
    · have h5 : 5 ≤ n := by omega
      have hpos := deficit_sixteen_nonneg_from_five n h5
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-16 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2` or
`n ≥ 4`. -/
theorem deficit_sixteen_pos (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : 0 < wick 16 n - E16 n := by
  rcases hn with rfl | hge
  · rw [deficit_sixteen]; norm_num
  · by_cases hn4 : n = 4
    · subst n
      rw [deficit_sixteen]
      norm_num
    · have hn5 : 5 ≤ n := by omega
      have hu0 : (0 : ℤ) ≤ n - 5 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_sixteen_factored_v n
      have hstrict : (0 : ℤ) < n * 8604831201382532874932469450 := by positivity
      have h1 : (0 : ℤ) ≤ n * (14022582233526125327422821285 * (n - 5) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (23653560298665624058210424220 * (n - 5) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (24487296934052178789102024210 * (n - 5) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (10942211359114512343896700125 * (n - 5) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (6054230223835569595019962125 * (n - 5) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (1901429695605631464287039025 * (n - 5) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (435045846827984935487919975 * (n - 5) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (112655488918450579360008750 * (n - 5) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (11667934210752197450572500 * (n - 5) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (2282933734214251059191250 * (n - 5) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (112701737908275193928250 * (n - 5) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (14901580237302158400000 * (n - 5) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (277613574132432037500 * (n - 5) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (23027854075501275000 * (n - 5) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

/-- The second coefficient law at depth 16: `23027854075501275000 = C(16,2)·31‼`. -/
theorem deficit_sixteen_leading :
    (23027854075501275000 : ℤ) = 120 * 191898783962510625 := by
  norm_num

end ProximityGap.Frontier.E16ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E16ClosedForm.E16_two
#print axioms ProximityGap.Frontier.E16ClosedForm.deficit_sixteen
#print axioms ProximityGap.Frontier.E16ClosedForm.E16_le_wick
#print axioms ProximityGap.Frontier.E16ClosedForm.deficit_sixteen_pos
