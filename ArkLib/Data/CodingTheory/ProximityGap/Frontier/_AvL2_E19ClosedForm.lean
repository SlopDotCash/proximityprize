/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_19(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_18`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 19`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 6`; the non-dyadic
integer `n = 5` is again a genuine Wick-bound exception, so the exported theorem uses the
honest dyadic-support-covering range `n = 2`, `n = 4`, or `n ≥ 6`. This is deliberately only
a char-0 rung; it does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E19ClosedForm

/-- `E_19(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 19`, in closed form. -/
def E19 (n : ℤ) : ℤ :=
  8200794532637891559375 * n ^ 19
    - 1402335865081079456653125 * n ^ 18
    + 116549691897849714841837500 * n ^ 17
    - 6230110803266875666090950000 * n ^ 16
    + 239117939249127481170401523750 * n ^ 15
    - 6972712816088177747222194811250 * n ^ 14
    + 159545676871235991176788000803750 * n ^ 13
    - 2919250199691414178814471652405000 * n ^ 12
    + 43157278180031149569660943227134625 * n ^ 11
    - 517628765234847234018407745369106125 * n ^ 10
    + 5031509102343806526928997094868035750 * n ^ 9
    - 39398902762056519388049591918021352000 * n ^ 8
    + 245715494832641659463655540741280703025 * n ^ 7
    - 1198718693084458817424467238629895896475 * n ^ 6
    + 4451525009586122916061470728229094858275 * n ^ 5
    - 12070562468377314183055653295634480192700 * n ^ 4
    + 22341437951478127036760957876636071704375 * n ^ 3
    - 24952609207466887760435912873842874861400 * n ^ 2
    + 12493977335125843571556554448614322144000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_nineteen (n : ℤ) : wick 19 n = 8200794532637891559375 * n ^ 19 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_19(2) = 35345263800 = C(38,19)`. -/
theorem E19_two : E19 2 = 35345263800 := by decide

/-- `E_19(4) = 1249287673091590440000`. -/
theorem E19_four : E19 4 = 1249287673091590440000 := by decide

/-! ## The exact char-0 deficit `D_19 = wick 19 n − E_19(ℂ)` -/

/-- The exact deficit `wick 19 n − E_19(ℂ)`. Its leading nonzero coefficient is
`C(19,2)·37‼ = 1402335865081079456653125`. -/
theorem deficit_nineteen (n : ℤ) :
    wick 19 n - E19 n =
      1402335865081079456653125 * n ^ 18
        - 116549691897849714841837500 * n ^ 17
        + 6230110803266875666090950000 * n ^ 16
        - 239117939249127481170401523750 * n ^ 15
        + 6972712816088177747222194811250 * n ^ 14
        - 159545676871235991176788000803750 * n ^ 13
        + 2919250199691414178814471652405000 * n ^ 12
        - 43157278180031149569660943227134625 * n ^ 11
        + 517628765234847234018407745369106125 * n ^ 10
        - 5031509102343806526928997094868035750 * n ^ 9
        + 39398902762056519388049591918021352000 * n ^ 8
        - 245715494832641659463655540741280703025 * n ^ 7
        + 1198718693084458817424467238629895896475 * n ^ 6
        - 4451525009586122916061470728229094858275 * n ^ 5
        + 12070562468377314183055653295634480192700 * n ^ 4
        - 22341437951478127036760957876636071704375 * n ^ 3
        + 24952609207466887760435912873842874861400 * n ^ 2
        - 12493977335125843571556554448614322144000 * n ^ 1 := by
  simp only [wick_nineteen, E19]; ring

/-- `wick 19 n − E_19 = n · (Σ_k c_k · (n-6)^k)` with all `c_k ≥ 0`. -/
theorem deficit_nineteen_factored_v (n : ℤ) :
    wick 19 n - E19 n =
      n * (        832872337210351698713239259565684900
        + 2921755961371587062061395733569854500 * (n - 6) ^ 1
        + 3004534658065975242335673236766900825 * (n - 6) ^ 2
        + 3330708719487292017036028173886217100 * (n - 6) ^ 3
        + 2017364349812548088272224239982290475 * (n - 6) ^ 4
        + 855202352646600496736126786413207575 * (n - 6) ^ 5
        + 353757948606831957328082432927796975 * (n - 6) ^ 6
        + 91131506445742341809645956434894000 * (n - 6) ^ 7
        + 21550783310004995836981130662222500 * (n - 6) ^ 8
        + 4236951513880001707402388220068625 * (n - 6) ^ 9
        + 542777431572092253571510986885375 * (n - 6) ^ 10
        + 83298208022650940416533641205000 * (n - 6) ^ 11
        + 5840194369627198078323344268750 * (n - 6) ^ 12
        + 664250952671645801921024816250 * (n - 6) ^ 13
        + 24072455909289511254256976250 * (n - 6) ^ 14
        + 1907176776510268061048250000 * (n - 6) ^ 15
        + 26488566340420389736781250 * (n - 6) ^ 16
        + 1402335865081079456653125 * (n - 6) ^ 17) := by
  rw [deficit_nineteen]; ring_nf

/-- `0 ≤ wick 19 n − E19 n` for `n ≥ 6`, from the nonnegative `v = n−6` certificate. -/
theorem deficit_nineteen_nonneg_from_six (n : ℤ) (hn : 6 ≤ n) :
    0 ≤ wick 19 n - E19 n := by
  have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 832872337210351698713239259565684900 := by positivity
  have h1 : (0 : ℤ) ≤ n * (2921755961371587062061395733569854500 * (n - 6) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (3004534658065975242335673236766900825 * (n - 6) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (3330708719487292017036028173886217100 * (n - 6) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (2017364349812548088272224239982290475 * (n - 6) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (855202352646600496736126786413207575 * (n - 6) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (353757948606831957328082432927796975 * (n - 6) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (91131506445742341809645956434894000 * (n - 6) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (21550783310004995836981130662222500 * (n - 6) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (4236951513880001707402388220068625 * (n - 6) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (542777431572092253571510986885375 * (n - 6) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (83298208022650940416533641205000 * (n - 6) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (5840194369627198078323344268750 * (n - 6) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (664250952671645801921024816250 * (n - 6) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (24072455909289511254256976250 * (n - 6) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (1907176776510268061048250000 * (n - 6) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (26488566340420389736781250 * (n - 6) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (1402335865081079456653125 * (n - 6) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  rw [deficit_nineteen_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

/-- Base case `n=2`. -/
theorem E19_le_wick_base_two : E19 2 ≤ wick 19 2 := by rw [E19_two, wick_nineteen]; norm_num

/-- Base case `n=4`. -/
theorem E19_le_wick_base_four : E19 4 ≤ wick 19 4 := by rw [E19_four, wick_nineteen]; norm_num

/-- The depth-19 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. -/
theorem E19_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) : E19 n ≤ wick 19 n := by
  rcases hn with rfl | hrest
  · exact E19_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E19_le_wick_base_four
    · have hpos := deficit_nineteen_nonneg_from_six n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-19 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. -/
theorem deficit_nineteen_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) :
    0 < wick 19 n - E19 n := by
  rcases hn with rfl | hrest
  · rw [deficit_nineteen]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_nineteen]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_nineteen_factored_v n
      have hstrict : (0 : ℤ) < n * 832872337210351698713239259565684900 := by positivity
      have h1 : (0 : ℤ) ≤ n * (2921755961371587062061395733569854500 * (n - 6) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (3004534658065975242335673236766900825 * (n - 6) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (3330708719487292017036028173886217100 * (n - 6) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (2017364349812548088272224239982290475 * (n - 6) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (855202352646600496736126786413207575 * (n - 6) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (353757948606831957328082432927796975 * (n - 6) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (91131506445742341809645956434894000 * (n - 6) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (21550783310004995836981130662222500 * (n - 6) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (4236951513880001707402388220068625 * (n - 6) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (542777431572092253571510986885375 * (n - 6) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (83298208022650940416533641205000 * (n - 6) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (5840194369627198078323344268750 * (n - 6) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (664250952671645801921024816250 * (n - 6) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (24072455909289511254256976250 * (n - 6) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (1907176776510268061048250000 * (n - 6) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (26488566340420389736781250 * (n - 6) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (1402335865081079456653125 * (n - 6) ^ 17) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

/-- The second coefficient law at depth 19: `1402335865081079456653125 = C(19,2)·37‼`. -/
theorem deficit_nineteen_leading :
    (1402335865081079456653125 : ℤ) = 171 * 8200794532637891559375 := by
  norm_num

end ProximityGap.Frontier.E19ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E19ClosedForm.E19_two
#print axioms ProximityGap.Frontier.E19ClosedForm.deficit_nineteen
#print axioms ProximityGap.Frontier.E19ClosedForm.E19_le_wick
#print axioms ProximityGap.Frontier.E19ClosedForm.deficit_nineteen_pos
