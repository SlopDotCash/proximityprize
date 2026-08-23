/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_22(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_21`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 22`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 7`, covering the dyadic
support range `n = 2`, `n = 4`, or `n ≥ 7`. This is deliberately only a char-0 rung; it
does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E22ClosedForm

/-- `E_22(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 22`, in closed form. -/
def E22 (n : ℤ) : ℤ :=
  563862029680583509947946875 * n ^ 22
    - 130252128856214790797975728125 * n ^ 21
    + 14689545643228668073327262671875 * n ^ 20
    - 1072409194249501777570000161562500 * n ^ 19
    + 56694204444567340357995642900170625 * n ^ 18
    - 2301679736337221474991409250346498750 * n ^ 17
    + 74296542675659145583955109764530162500 * n ^ 16
    - 1948700922297234742770229930714693312500 * n ^ 15
    + 42103240420419216436342477538550253834125 * n ^ 14
    - 755479695172657506875624968429716410331375 * n ^ 13
    + 11303128142056514282380387478004639254542875 * n ^ 12
    - 141080415523956342046057570390140494480111250 * n ^ 11
    + 1465086902146952483886768748815693400401295950 * n ^ 10
    - 12583844375355663831650187995643556987749136425 * n ^ 9
    + 88543803416490604903442461788419779956123876300 * n ^ 8
    - 503263186837470796377393493818286802812887868200 * n ^ 7
    + 2264751581222669852559754984205316710689884933615 * n ^ 6
    - 7840430177436637556992683155784108387219492201555 * n ^ 5
    + 20006796394314027388941982642439351198917227417045 * n ^ 4
    - 35149651808759668087323189858676368021286627187745 * n ^ 3
    + 37568040256683269196612925706409555929790368409240 * n ^ 2
    - 18146338695700452594305259346212040085684336784000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twentytwo (n : ℤ) : wick 22 n = 563862029680583509947946875 * n ^ 22 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_22(2) = 2104098963720 = C(44,22)`. -/
theorem E22_two : E22 2 = 2104098963720 := by decide

/-- `E_22(4) = 4427232449127577876238400`. -/
theorem E22_four : E22 4 = 4427232449127577876238400 := by decide

/-! ## The exact char-0 deficit `D_22 = wick 22 n − E_22(ℂ)` -/

/-- The exact deficit `wick 22 n − E_22(ℂ)`. Its leading nonzero coefficient is
`C(22,2)·43‼ = 130252128856214790797975728125`. -/
theorem deficit_twentytwo (n : ℤ) :
    wick 22 n - E22 n =
  130252128856214790797975728125 * n ^ 21
    - 14689545643228668073327262671875 * n ^ 20
    + 1072409194249501777570000161562500 * n ^ 19
    - 56694204444567340357995642900170625 * n ^ 18
    + 2301679736337221474991409250346498750 * n ^ 17
    - 74296542675659145583955109764530162500 * n ^ 16
    + 1948700922297234742770229930714693312500 * n ^ 15
    - 42103240420419216436342477538550253834125 * n ^ 14
    + 755479695172657506875624968429716410331375 * n ^ 13
    - 11303128142056514282380387478004639254542875 * n ^ 12
    + 141080415523956342046057570390140494480111250 * n ^ 11
    - 1465086902146952483886768748815693400401295950 * n ^ 10
    + 12583844375355663831650187995643556987749136425 * n ^ 9
    - 88543803416490604903442461788419779956123876300 * n ^ 8
    + 503263186837470796377393493818286802812887868200 * n ^ 7
    - 2264751581222669852559754984205316710689884933615 * n ^ 6
    + 7840430177436637556992683155784108387219492201555 * n ^ 5
    - 20006796394314027388941982642439351198917227417045 * n ^ 4
    + 35149651808759668087323189858676368021286627187745 * n ^ 3
    - 37568040256683269196612925706409555929790368409240 * n ^ 2
    + 18146338695700452594305259346212040085684336784000 * n ^ 1 := by
  simp only [wick_twentytwo, E22]; ring

/-- `wick 22 n − E_22 = n · (Σ_k c_k · (n-7)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twentytwo_factored_v (n : ℤ) :
    wick 22 n - E22 n =
      n * (      244615557849075186281980997386227512194408815
        + 1032510749398052854567432935212987082012116610 * (n - 7) ^ 1
        + 1379093544270042941464456966282944506115431670 * (n - 7) ^ 2
        + 1139359263372059073804165499067322607287988545 * (n - 7) ^ 3
        + 828565504058181861604536206142638619114549255 * (n - 7) ^ 4
        + 373956447128384302045498025542694875868696160 * (n - 7) ^ 5
        + 143122653242872100854393421646201944403549450 * (n - 7) ^ 6
        + 45948557344454817083827926074006612475375450 * (n - 7) ^ 7
        + 10740478758266939740515386370573121093554450 * (n - 7) ^ 8
        + 2339844684449996285934892787703480270776550 * (n - 7) ^ 9
        + 394461690039601328815380616588278575603625 * (n - 7) ^ 10
        + 54463443632752531943319857868090058858125 * (n - 7) ^ 11
        + 7084826192677151272707923698965914327250 * (n - 7) ^ 12
        + 603255422711417802825389439361916478375 * (n - 7) ^ 13
        + 60294461342105541600393754665517762500 * (n - 7) ^ 14
        + 3071451165391917223690448740481415000 * (n - 7) ^ 15
        + 227803745823614025364934603037444375 * (n - 7) ^ 16
        + 6276838511613981327239712740501250 * (n - 7) ^ 17
        + 331346943351448626146628255046875 * (n - 7) ^ 18
        + 3545752396641402638389339265625 * (n - 7) ^ 19
        + 130252128856214790797975728125 * (n - 7) ^ 20) := by
  rw [deficit_twentytwo]; ring_nf

/-- `0 ≤ wick 22 n − E22 n` for `n ≥ 7`, from the nonnegative `v = n−7` certificate. -/
theorem deficit_twentytwo_nonneg_from_seven (n : ℤ) (hn : 7 ≤ n) :
    0 ≤ wick 22 n - E22 n := by
  have hu0 : (0 : ℤ) ≤ n - 7 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 244615557849075186281980997386227512194408815 := by positivity
  have h1 : (0 : ℤ) ≤ n * (1032510749398052854567432935212987082012116610 * (n - 7) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (1379093544270042941464456966282944506115431670 * (n - 7) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (1139359263372059073804165499067322607287988545 * (n - 7) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (828565504058181861604536206142638619114549255 * (n - 7) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (373956447128384302045498025542694875868696160 * (n - 7) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (143122653242872100854393421646201944403549450 * (n - 7) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (45948557344454817083827926074006612475375450 * (n - 7) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (10740478758266939740515386370573121093554450 * (n - 7) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (2339844684449996285934892787703480270776550 * (n - 7) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (394461690039601328815380616588278575603625 * (n - 7) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (54463443632752531943319857868090058858125 * (n - 7) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (7084826192677151272707923698965914327250 * (n - 7) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (603255422711417802825389439361916478375 * (n - 7) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (60294461342105541600393754665517762500 * (n - 7) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (3071451165391917223690448740481415000 * (n - 7) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (227803745823614025364934603037444375 * (n - 7) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (6276838511613981327239712740501250 * (n - 7) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (331346943351448626146628255046875 * (n - 7) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  have h19 : (0 : ℤ) ≤ n * (3545752396641402638389339265625 * (n - 7) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
  have h20 : (0 : ℤ) ≤ n * (130252128856214790797975728125 * (n - 7) ^ 20) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
  rw [deficit_twentytwo_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

/-- Base case `n=2`. -/
theorem E22_le_wick_base_two : E22 2 ≤ wick 22 2 := by rw [E22_two, wick_twentytwo]; norm_num

/-- Base case `n=4`. -/
theorem E22_le_wick_base_four : E22 4 ≤ wick 22 4 := by rw [E22_four, wick_twentytwo]; norm_num

/-- The depth-22 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 7`. -/
theorem E22_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 7 ≤ n) : E22 n ≤ wick 22 n := by
  rcases hn with rfl | hrest
  · exact E22_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E22_le_wick_base_four
    · have hpos := deficit_twentytwo_nonneg_from_seven n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-22 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 7`. -/
theorem deficit_twentytwo_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 7 ≤ n) :
    0 < wick 22 n - E22 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twentytwo]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_twentytwo]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 7 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_twentytwo_factored_v n
      have hstrict : (0 : ℤ) < n * 244615557849075186281980997386227512194408815 := by positivity
      have h1 : (0 : ℤ) ≤ n * (1032510749398052854567432935212987082012116610 * (n - 7) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (1379093544270042941464456966282944506115431670 * (n - 7) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (1139359263372059073804165499067322607287988545 * (n - 7) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (828565504058181861604536206142638619114549255 * (n - 7) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (373956447128384302045498025542694875868696160 * (n - 7) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (143122653242872100854393421646201944403549450 * (n - 7) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (45948557344454817083827926074006612475375450 * (n - 7) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (10740478758266939740515386370573121093554450 * (n - 7) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (2339844684449996285934892787703480270776550 * (n - 7) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (394461690039601328815380616588278575603625 * (n - 7) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (54463443632752531943319857868090058858125 * (n - 7) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (7084826192677151272707923698965914327250 * (n - 7) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (603255422711417802825389439361916478375 * (n - 7) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (60294461342105541600393754665517762500 * (n - 7) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (3071451165391917223690448740481415000 * (n - 7) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (227803745823614025364934603037444375 * (n - 7) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (6276838511613981327239712740501250 * (n - 7) ^ 17) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      have h18 : (0 : ℤ) ≤ n * (331346943351448626146628255046875 * (n - 7) ^ 18) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
      have h19 : (0 : ℤ) ≤ n * (3545752396641402638389339265625 * (n - 7) ^ 19) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
      have h20 : (0 : ℤ) ≤ n * (130252128856214790797975728125 * (n - 7) ^ 20) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8,
        h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

/-- The second coefficient law at depth 22: `130252128856214790797975728125 = C(22,2)·43‼`. -/
theorem deficit_twentytwo_leading :
    (130252128856214790797975728125 : ℤ) = 231 * 563862029680583509947946875 := by
  norm_num

end ProximityGap.Frontier.E22ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E22ClosedForm.E22_two
#print axioms ProximityGap.Frontier.E22ClosedForm.deficit_twentytwo
#print axioms ProximityGap.Frontier.E22ClosedForm.E22_le_wick
#print axioms ProximityGap.Frontier.E22ClosedForm.deficit_twentytwo_pos
