/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_17(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder to the next unheld depth after `E_16`.
It records the exact cross-polytope / Lam--Leung polynomial at depth `r = 17`, plus the
Wick bound and strict positive cushion. The positivity certificate starts at `n = 6`:
there is a real non-dyadic exception at `n = 5`, so the exported Wick theorem is stated on
`n = 2`, `n = 4`, or `n ≥ 6`. This is deliberately only a char-0 rung; it does not assert
the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E17ClosedForm

/-- `E_17(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 17`, in closed form. -/
def E17 (n : ℤ) : ℤ :=
  6332659870762850625 * n ^ 17
    - 861241742423747685000 * n ^ 16
    + 56698414709563389262500 * n ^ 15
    - 2386357327965800877187500 * n ^ 14
    + 71535825247247205997902750 * n ^ 13
    - 1612429526974175593725541500 * n ^ 12
    + 28150211762125878308297163750 * n ^ 11
    - 386693375071741990355872518750 * n ^ 10
    + 4206607537109477912437554854325 * n ^ 9
    - 36205803397568814509765398032900 * n ^ 8
    + 244632253220564312016557214520950 * n ^ 7
    - 1277701917161411899971325158396750 * n ^ 6
    + 5029351053630257652718337264125845 * n ^ 5
    - 14331000797454893252233163153843430 * n ^ 4
    + 27661959171426661768797765101443755 * n ^ 3
    - 31993133900775415850383518575485395 * n ^ 2
    + 16476458169858956641176546301560000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_seventeen (n : ℤ) : wick 17 n = 6332659870762850625 * n ^ 17 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_17(2) = 2333606220 = C(34,17)`. -/
theorem E17_two : E17 2 = 2333606220 := by decide

/-- `E_17(4) = 5445717990022688400`. -/
theorem E17_four : E17 4 = 5445717990022688400 := by decide

/-! ## The exact char-0 deficit `D_17 = wick 17 n − E_17(ℂ)` -/

/-- The exact deficit `wick 17 n − E_17(ℂ)`. Its leading nonzero coefficient is
`C(17,2)·33‼ = 861241742423747685000`. -/
theorem deficit_seventeen (n : ℤ) :
    wick 17 n - E17 n =
      861241742423747685000 * n ^ 16
        - 56698414709563389262500 * n ^ 15
        + 2386357327965800877187500 * n ^ 14
        - 71535825247247205997902750 * n ^ 13
        + 1612429526974175593725541500 * n ^ 12
        - 28150211762125878308297163750 * n ^ 11
        + 386693375071741990355872518750 * n ^ 10
        - 4206607537109477912437554854325 * n ^ 9
        + 36205803397568814509765398032900 * n ^ 8
        - 244632253220564312016557214520950 * n ^ 7
        + 1277701917161411899971325158396750 * n ^ 6
        - 5029351053630257652718337264125845 * n ^ 5
        + 14331000797454893252233163153843430 * n ^ 4
        - 27661959171426661768797765101443755 * n ^ 3
        + 31993133900775415850383518575485395 * n ^ 2
        - 16476458169858956641176546301560000 * n ^ 1 := by
  simp only [wick_seventeen, E17]; ring

/-- `wick 17 n − E_17 = n · (Σ_k c_k · (n-6)^k)` with all `c_k ≥ 0`. -/
theorem deficit_seventeen_factored_v (n : ℤ) :
    wick 17 n - E17 n =
      n * (        17865129346473914509291477942950
        + 48409936467582706395462663604695 * (n - 6) ^ 1
        + 58616157963109539165927907640265 * (n - 6) ^ 2
        + 46603291424717374262940427825950 * (n - 6) ^ 3
        + 25197218466838591683535167863655 * (n - 6) ^ 4
        + 9926630299937133655790287119750 * (n - 6) ^ 5
        + 3101313787269067030715457653250 * (n - 6) ^ 6
        + 725609949471274061484907917300 * (n - 6) ^ 7
        + 136325262159210450006268763175 * (n - 6) ^ 8
        + 20658736227690975427847583750 * (n - 6) ^ 9
        + 2277138328696364960698121250 * (n - 6) ^ 10
        + 228456419992940312316643500 * (n - 6) ^ 11
        + 13498878190961521680572250 * (n - 6) ^ 12
        + 879184278724242428437500 * (n - 6) ^ 13
        + 20813342108573902387500 * (n - 6) ^ 14
        + 861241742423747685000 * (n - 6) ^ 15) := by
  rw [deficit_seventeen]; ring_nf

/-- `0 ≤ wick 17 n − E17 n` for `n ≥ 6`, from the nonnegative `v = n−6` certificate. -/
theorem deficit_seventeen_nonneg_from_six (n : ℤ) (hn : 6 ≤ n) :
    0 ≤ wick 17 n - E17 n := by
  have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_seventeen_factored_v]
  have h0 : (0 : ℤ) ≤ n * 17865129346473914509291477942950 := by positivity
  have h1 : (0 : ℤ) ≤ n * (48409936467582706395462663604695 * (n - 6) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (58616157963109539165927907640265 * (n - 6) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (46603291424717374262940427825950 * (n - 6) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (25197218466838591683535167863655 * (n - 6) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (9926630299937133655790287119750 * (n - 6) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (3101313787269067030715457653250 * (n - 6) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (725609949471274061484907917300 * (n - 6) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (136325262159210450006268763175 * (n - 6) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (20658736227690975427847583750 * (n - 6) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (2277138328696364960698121250 * (n - 6) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (228456419992940312316643500 * (n - 6) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (13498878190961521680572250 * (n - 6) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (879184278724242428437500 * (n - 6) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (20813342108573902387500 * (n - 6) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (861241742423747685000 * (n - 6) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

/-- Base case `n=2`. -/
theorem E17_le_wick_base_two : E17 2 ≤ wick 17 2 := by rw [E17_two, wick_seventeen]; norm_num

/-- Base case `n=4`. -/
theorem E17_le_wick_base_four : E17 4 ≤ wick 17 4 := by rw [E17_four, wick_seventeen]; norm_num

/-- The depth-17 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. The non-dyadic integer `n = 5` is a genuine exception to this
Wick bound, so it is intentionally excluded rather than hidden. -/
theorem E17_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) : E17 n ≤ wick 17 n := by
  rcases hn with rfl | hrest
  · exact E17_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E17_le_wick_base_four
    · have hpos := deficit_seventeen_nonneg_from_six n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-17 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. -/
theorem deficit_seventeen_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) :
    0 < wick 17 n - E17 n := by
  rcases hn with rfl | hrest
  · rw [deficit_seventeen]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_seventeen]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_seventeen_factored_v n
      have hstrict : (0 : ℤ) < n * 17865129346473914509291477942950 := by positivity
      have h1 : (0 : ℤ) ≤ n * (48409936467582706395462663604695 * (n - 6) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (58616157963109539165927907640265 * (n - 6) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (46603291424717374262940427825950 * (n - 6) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (25197218466838591683535167863655 * (n - 6) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (9926630299937133655790287119750 * (n - 6) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (3101313787269067030715457653250 * (n - 6) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (725609949471274061484907917300 * (n - 6) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (136325262159210450006268763175 * (n - 6) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (20658736227690975427847583750 * (n - 6) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (2277138328696364960698121250 * (n - 6) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (228456419992940312316643500 * (n - 6) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (13498878190961521680572250 * (n - 6) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (879184278724242428437500 * (n - 6) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (20813342108573902387500 * (n - 6) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (861241742423747685000 * (n - 6) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

/-- The second coefficient law at depth 17: `861241742423747685000 = C(17,2)·33‼`. -/
theorem deficit_seventeen_leading :
    (861241742423747685000 : ℤ) = 136 * 6332659870762850625 := by
  norm_num

end ProximityGap.Frontier.E17ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E17ClosedForm.E17_two
#print axioms ProximityGap.Frontier.E17ClosedForm.deficit_seventeen
#print axioms ProximityGap.Frontier.E17ClosedForm.E17_le_wick
#print axioms ProximityGap.Frontier.E17ClosedForm.deficit_seventeen_pos
