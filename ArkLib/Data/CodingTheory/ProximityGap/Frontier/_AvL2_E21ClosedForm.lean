/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_21(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_20`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 21`, plus the Wick bound and a
strict positive cushion. The non-dyadic integer `n = 5` is a genuine Wick-bound exception;
the exported theorem uses the honest dyadic-support-covering range `n = 2`, `n = 4`, or
`n ≥ 8`. This is deliberately only a char-0 rung; it does not assert the char-p transfer
that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E21ClosedForm

/-- `E_21(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 21`, in closed form. -/
def E21 (n : ℤ) : ℤ :=
  13113070457687988603440625 * n ^ 21
    - 2753744796114477606722531250 * n ^ 20
    + 281952869957721234954979171875 * n ^ 19
    - 18652490376481414069135065421875 * n ^ 18
    + 891353129738844905335285548716250 * n ^ 17
    - 32609801570893590776990720237775000 * n ^ 16
    + 944985478498936708683774318531637500 * n ^ 15
    - 22150398433161956192219195478529762500 * n ^ 14
    + 425373415033841078822441825280295791375 * n ^ 13
    - 6740212274869971313507184804891951520750 * n ^ 12
    + 88361024303482640494795072176303348534375 * n ^ 11
    - 957309520937115906914371186188082161223125 * n ^ 10
    + 8530620807120361545673783873207556938196775 * n ^ 9
    - 61982724059531621276630752394520293433017700 * n ^ 8
    + 362337636957814012510645689797387544698703900 * n ^ 7
    - 1671212141283465250260064843973178766689447750 * n ^ 6
    + 5911588541630385473588044208606794529565121005 * n ^ 5
    - 15370426158551423885505400004595639575100884130 * n ^ 4
    + 27444506147783101261751439506741708081967856785 * n ^ 3
    - 29738048292893439919854444867461850283203902880 * n ^ 2
    + 14527083502748197554786323293381828415083526400 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twentyone (n : ℤ) : wick 21 n = 13113070457687988603440625 * n ^ 21 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_21(2) = 538257874440 = C(42,21)`. -/
theorem E21_two : E21 2 = 538257874440 := by decide

/-- `E_21(4) = 289721539396666805313600`. -/
theorem E21_four : E21 4 = 289721539396666805313600 := by decide

/-! ## The exact char-0 deficit `D_21 = wick 21 n − E_21(ℂ)` -/

/-- The exact deficit `wick 21 n − E_21(ℂ)`. Its leading nonzero coefficient is
`C(21,2)·41‼ = 2753744796114477606722531250`. -/
theorem deficit_twentyone (n : ℤ) :
    wick 21 n - E21 n =
      2753744796114477606722531250 * n ^ 20
        - 281952869957721234954979171875 * n ^ 19
        + 18652490376481414069135065421875 * n ^ 18
        - 891353129738844905335285548716250 * n ^ 17
        + 32609801570893590776990720237775000 * n ^ 16
        - 944985478498936708683774318531637500 * n ^ 15
        + 22150398433161956192219195478529762500 * n ^ 14
        - 425373415033841078822441825280295791375 * n ^ 13
        + 6740212274869971313507184804891951520750 * n ^ 12
        - 88361024303482640494795072176303348534375 * n ^ 11
        + 957309520937115906914371186188082161223125 * n ^ 10
        - 8530620807120361545673783873207556938196775 * n ^ 9
        + 61982724059531621276630752394520293433017700 * n ^ 8
        - 362337636957814012510645689797387544698703900 * n ^ 7
        + 1671212141283465250260064843973178766689447750 * n ^ 6
        - 5911588541630385473588044208606794529565121005 * n ^ 5
        + 15370426158551423885505400004595639575100884130 * n ^ 4
        - 27444506147783101261751439506741708081967856785 * n ^ 3
        + 29738048292893439919854444867461850283203902880 * n ^ 2
        - 14527083502748197554786323293381828415083526400 * n ^ 1 := by
  simp only [wick_twentyone, E21]; ring

/-- `wick 21 n − E_21 = n · (Σ_k c_k · (n-8)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twentyone_factored_v (n : ℤ) :
    wick 21 n - E21 n =
      n * (        15118340917320415480606012885520896079954880
        + 37764298036260587789807670917852294574401040 * (n - 8) ^ 1
        + 44918970306961558632963626053870838265661215 * (n - 8) ^ 2
        + 33652874463450972570076029952162327441888770 * (n - 8) ^ 3
        + 17877261493834119094399865981125987805140995 * (n - 8) ^ 4
        + 7157514798200274560021244609378294544844550 * (n - 8) ^ 5
        + 2234239567318400525002774548026900613346500 * (n - 8) ^ 6
        + 558882873042766953758464136351834204072100 * (n - 8) ^ 7
        + 113569036141545922054678227851233612788225 * (n - 8) ^ 8
        + 18901533649109072590535321121393595033125 * (n - 8) ^ 9
        + 2604009627256727902871142918481626203625 * (n - 8) ^ 10
        + 295473355253825357602807440198730908750 * (n - 8) ^ 11
        + 27684008387587071954925241422555508625 * (n - 8) ^ 12
        + 2140513409684060753817443409103162500 * (n - 8) ^ 13
        + 131969321551179291441115363572562500 * (n - 8) ^ 14
        + 6788940498453274231692272746095000 * (n - 8) ^ 15
        + 250712957043304621455963281658750 * (n - 8) ^ 16
        + 8188260151246399163589446671875 * (n - 8) ^ 17
        + 136616339051679361266845578125 * (n - 8) ^ 18
        + 2753744796114477606722531250 * (n - 8) ^ 19) := by
  rw [deficit_twentyone]; ring_nf

/-- `0 ≤ wick 21 n − E21 n` for `n ≥ 8`, from the nonnegative `v = n−8` certificate. -/
theorem deficit_twentyone_nonneg_from_eight (n : ℤ) (hn : 8 ≤ n) :
    0 ≤ wick 21 n - E21 n := by
  have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 15118340917320415480606012885520896079954880 := by positivity
  have h1 : (0 : ℤ) ≤ n * (37764298036260587789807670917852294574401040 * (n - 8) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (44918970306961558632963626053870838265661215 * (n - 8) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (33652874463450972570076029952162327441888770 * (n - 8) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (17877261493834119094399865981125987805140995 * (n - 8) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (7157514798200274560021244609378294544844550 * (n - 8) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (2234239567318400525002774548026900613346500 * (n - 8) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (558882873042766953758464136351834204072100 * (n - 8) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (113569036141545922054678227851233612788225 * (n - 8) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (18901533649109072590535321121393595033125 * (n - 8) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (2604009627256727902871142918481626203625 * (n - 8) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (295473355253825357602807440198730908750 * (n - 8) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (27684008387587071954925241422555508625 * (n - 8) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (2140513409684060753817443409103162500 * (n - 8) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (131969321551179291441115363572562500 * (n - 8) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (6788940498453274231692272746095000 * (n - 8) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (250712957043304621455963281658750 * (n - 8) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (8188260151246399163589446671875 * (n - 8) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (136616339051679361266845578125 * (n - 8) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  have h19 : (0 : ℤ) ≤ n * (2753744796114477606722531250 * (n - 8) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
  rw [deficit_twentyone_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

/-- Base case `n=2`. -/
theorem E21_le_wick_base_two : E21 2 ≤ wick 21 2 := by rw [E21_two, wick_twentyone]; norm_num

/-- Base case `n=4`. -/
theorem E21_le_wick_base_four : E21 4 ≤ wick 21 4 := by rw [E21_four, wick_twentyone]; norm_num

/-- The depth-21 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem E21_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) : E21 n ≤ wick 21 n := by
  rcases hn with rfl | hrest
  · exact E21_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E21_le_wick_base_four
    · have hpos := deficit_twentyone_nonneg_from_eight n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-21 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem deficit_twentyone_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) :
    0 < wick 21 n - E21 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twentyone]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_twentyone]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_twentyone_factored_v n
      have hstrict : (0 : ℤ) < n * 15118340917320415480606012885520896079954880 := by positivity
      have h1 : (0 : ℤ) ≤ n * (37764298036260587789807670917852294574401040 * (n - 8) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (44918970306961558632963626053870838265661215 * (n - 8) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (33652874463450972570076029952162327441888770 * (n - 8) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (17877261493834119094399865981125987805140995 * (n - 8) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (7157514798200274560021244609378294544844550 * (n - 8) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (2234239567318400525002774548026900613346500 * (n - 8) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (558882873042766953758464136351834204072100 * (n - 8) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (113569036141545922054678227851233612788225 * (n - 8) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (18901533649109072590535321121393595033125 * (n - 8) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (2604009627256727902871142918481626203625 * (n - 8) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (295473355253825357602807440198730908750 * (n - 8) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (27684008387587071954925241422555508625 * (n - 8) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (2140513409684060753817443409103162500 * (n - 8) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (131969321551179291441115363572562500 * (n - 8) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (6788940498453274231692272746095000 * (n - 8) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (250712957043304621455963281658750 * (n - 8) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (8188260151246399163589446671875 * (n - 8) ^ 17) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      have h18 : (0 : ℤ) ≤ n * (136616339051679361266845578125 * (n - 8) ^ 18) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
      have h19 : (0 : ℤ) ≤ n * (2753744796114477606722531250 * (n - 8) ^ 19) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8,
        h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

/-- The second coefficient law at depth 21: `2753744796114477606722531250 = C(21,2)·41‼`. -/
theorem deficit_twentyone_leading :
    (2753744796114477606722531250 : ℤ) = 210 * 13113070457687988603440625 := by
  norm_num

end ProximityGap.Frontier.E21ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E21ClosedForm.E21_two
#print axioms ProximityGap.Frontier.E21ClosedForm.deficit_twentyone
#print axioms ProximityGap.Frontier.E21ClosedForm.E21_le_wick
#print axioms ProximityGap.Frontier.E21ClosedForm.deficit_twentyone_pos
