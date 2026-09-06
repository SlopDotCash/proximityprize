/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_25(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E24`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 25`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 8`, covering the dyadic
support range `n = 2`, `n = 4`, or `n ≥ 8`. This is deliberately only a char-0 rung; it
does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E25ClosedForm

/-- `E_25(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 25`, in closed form. -/
def E25 (n : ℤ) : ℤ :=
  58435841445947272053455474390625 * n ^ 25
    - 17530752433784181616036642317187500 * n ^ 24
    + 2576046677075508909689828829386718750 * n ^ 23
    - 246158060298980586161578513096788281250 * n ^ 22
    + 17133795237114937077700982746965369046875 * n ^ 21
    - 922531630300981517099478247117837803281250 * n ^ 20
    + 39842201579012067166072661989480558812890625 * n ^ 19
    - 1412872022057605561388824802478114064029140625 * n ^ 18
    + 41785446200755715220013565486645202303721021875 * n ^ 17
    - 1041375971204729234674918509327221175377762475000 * n ^ 16
    + 22014581026376841255171220566725324853554965500000 * n ^ 15
    - 396205395248164945238390472365459721422060951062500 * n ^ 14
    + 6077954965768417317816725790356763903575024092942500 * n ^ 13
    - 79392055002490292086528192724652925813441664692965000 * n ^ 12
    + 880219924627592760385096753061570152517884158696217500 * n ^ 11
    - 8237893445981540425756699219321823871257992842805875000 * n ^ 10
    + 64556048768723194008695273918040542097135065823052367625 * n ^ 9
    - 418853620024171809141766896288514716072321453945210274500 * n ^ 8
    + 2215715224027308761028676544670359527310056240246018317750 * n ^ 7
    - 9356992924764936745083976750661759806089358745094852589500 * n ^ 6
    + 30625567849088336007588974106009899146865218911360888746445 * n ^ 5
    - 74390787213087215476395016684306809875070650353381561283700 * n ^ 4
    + 125213047328468054789187664586011533542616283246472555565375 * n ^ 3
    - 129013541889199535228177177567547708369929134154478043375800 * n ^ 2
    + 60454093171740412788772609460692147460744344538302841907456 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twentyfive (n : ℤ) : wick 25 n = 58435841445947272053455474390625 * n ^ 25 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_25(2) = 126410606437752 = C(50,25)`. -/
theorem E25_two : E25 2 = 126410606437752 := by decide

/-- `E_25(4) = 15979641419960227387050813504`. -/
theorem E25_four : E25 4 = 15979641419960227387050813504 := by decide

/-! ## The exact char-0 deficit `D_25 = wick 25 n − E_25(ℂ)` -/

/-- The exact deficit `wick 25 n − E_25(ℂ)`. Its leading nonzero coefficient is
`C(25,2)·49‼ = 17530752433784181616036642317187500`. -/
theorem deficit_twentyfive (n : ℤ) :
    wick 25 n - E25 n =
  17530752433784181616036642317187500 * n ^ 24
    - 2576046677075508909689828829386718750 * n ^ 23
    + 246158060298980586161578513096788281250 * n ^ 22
    - 17133795237114937077700982746965369046875 * n ^ 21
    + 922531630300981517099478247117837803281250 * n ^ 20
    - 39842201579012067166072661989480558812890625 * n ^ 19
    + 1412872022057605561388824802478114064029140625 * n ^ 18
    - 41785446200755715220013565486645202303721021875 * n ^ 17
    + 1041375971204729234674918509327221175377762475000 * n ^ 16
    - 22014581026376841255171220566725324853554965500000 * n ^ 15
    + 396205395248164945238390472365459721422060951062500 * n ^ 14
    - 6077954965768417317816725790356763903575024092942500 * n ^ 13
    + 79392055002490292086528192724652925813441664692965000 * n ^ 12
    - 880219924627592760385096753061570152517884158696217500 * n ^ 11
    + 8237893445981540425756699219321823871257992842805875000 * n ^ 10
    - 64556048768723194008695273918040542097135065823052367625 * n ^ 9
    + 418853620024171809141766896288514716072321453945210274500 * n ^ 8
    - 2215715224027308761028676544670359527310056240246018317750 * n ^ 7
    + 9356992924764936745083976750661759806089358745094852589500 * n ^ 6
    - 30625567849088336007588974106009899146865218911360888746445 * n ^ 5
    + 74390787213087215476395016684306809875070650353381561283700 * n ^ 4
    - 125213047328468054789187664586011533542616283246472555565375 * n ^ 3
    + 129013541889199535228177177567547708369929134154478043375800 * n ^ 2
    - 60454093171740412788772609460692147460744344538302841907456 * n ^ 1 := by
  simp only [wick_twentyfive, E25]; ring

/-- `wick 25 n − E_25 = n · (Σ_k c_k · (n-8)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twentyfive_factored_v (n : ℤ) :
    wick 25 n - E25 n =
      n * (      275955459042569551165547242704839136576119746893882624
        + 760960739831712805159513442906806138387120565155152840 * (n - 8) ^ 1
        + 1272578881276923350922927506139263845287184096090240545 * (n - 8) ^ 2
        + 1065250257992024808380129736086886669629467089044021460 * (n - 8) ^ 3
        + 705783916854641885947025146496925275911029660576993555 * (n - 8) ^ 4
        + 368051189781838549250867426096933680923025228446841500 * (n - 8) ^ 5
        + 138523500039981943279329168375799845238326463366430250 * (n - 8) ^ 6
        + 45860027484907612427139969580797090593001765729466500 * (n - 8) ^ 7
        + 12195152941438960477184659712783395459169184065832375 * (n - 8) ^ 8
        + 2642472733891246244886458630030310165552658998075000 * (n - 8) ^ 9
        + 513052627672695478153867500666666046780432562782500 * (n - 8) ^ 10
        + 79291757660525362945268320349557483466498348085000 * (n - 8) ^ 11
        + 10846580999894968378851902386862724579664289557500 * (n - 8) ^ 12
        + 1274524585357430056510552592094892777652135062500 * (n - 8) ^ 13
        + 118696563051890027875601042661589757420203500000 * (n - 8) ^ 14
        + 10819126155501768942485797367874363072039675000 * (n - 8) ^ 15
        + 666391577429557198123627901167432081617103125 * (n - 8) ^ 16
        + 46591354576256319727087508224079310402890625 * (n - 8) ^ 17
        + 1804910609174240332952229015900518075859375 * (n - 8) ^ 18
        + 94169232073940367514878288005149255781250 * (n - 8) ^ 19
        + 2032529650068151925294235534036212203125 * (n - 8) ^ 20
        + 76631788541524486783033951524625781250 * (n - 8) ^ 21
        + 649611770740780507660913356975781250 * (n - 8) ^ 22
        + 17530752433784181616036642317187500 * (n - 8) ^ 23) := by
  rw [deficit_twentyfive]; ring_nf

/-- `0 ≤ wick 25 n − E25 n` for `n ≥ 8`, from the nonnegative `v = n−8` certificate. -/
theorem deficit_twentyfive_nonneg_from_8 (n : ℤ) (hn : 8 ≤ n) :
    0 ≤ wick 25 n - E25 n := by
  have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 275955459042569551165547242704839136576119746893882624 := by positivity
  have h1 : (0 : ℤ) ≤ n * (760960739831712805159513442906806138387120565155152840 * (n - 8) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (1272578881276923350922927506139263845287184096090240545 * (n - 8) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (1065250257992024808380129736086886669629467089044021460 * (n - 8) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (705783916854641885947025146496925275911029660576993555 * (n - 8) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (368051189781838549250867426096933680923025228446841500 * (n - 8) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (138523500039981943279329168375799845238326463366430250 * (n - 8) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (45860027484907612427139969580797090593001765729466500 * (n - 8) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (12195152941438960477184659712783395459169184065832375 * (n - 8) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (2642472733891246244886458630030310165552658998075000 * (n - 8) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (513052627672695478153867500666666046780432562782500 * (n - 8) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (79291757660525362945268320349557483466498348085000 * (n - 8) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (10846580999894968378851902386862724579664289557500 * (n - 8) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (1274524585357430056510552592094892777652135062500 * (n - 8) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (118696563051890027875601042661589757420203500000 * (n - 8) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (10819126155501768942485797367874363072039675000 * (n - 8) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (666391577429557198123627901167432081617103125 * (n - 8) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (46591354576256319727087508224079310402890625 * (n - 8) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (1804910609174240332952229015900518075859375 * (n - 8) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  have h19 : (0 : ℤ) ≤ n * (94169232073940367514878288005149255781250 * (n - 8) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
  have h20 : (0 : ℤ) ≤ n * (2032529650068151925294235534036212203125 * (n - 8) ^ 20) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
  have h21 : (0 : ℤ) ≤ n * (76631788541524486783033951524625781250 * (n - 8) ^ 21) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
  have h22 : (0 : ℤ) ≤ n * (649611770740780507660913356975781250 * (n - 8) ^ 22) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
  have h23 : (0 : ℤ) ≤ n * (17530752433784181616036642317187500 * (n - 8) ^ 23) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 23))
  rw [deficit_twentyfive_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]

/-- Base case `n=2`. -/
theorem E25_le_wick_base_two : E25 2 ≤ wick 25 2 := by rw [E25_two, wick_twentyfive]; norm_num

/-- Base case `n=4`. -/
theorem E25_le_wick_base_four : E25 4 ≤ wick 25 4 := by rw [E25_four, wick_twentyfive]; norm_num

/-- The depth-25 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem E25_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) : E25 n ≤ wick 25 n := by
  rcases hn with rfl | hrest
  · exact E25_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E25_le_wick_base_four
    · have hpos := deficit_twentyfive_nonneg_from_8 n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-25 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem deficit_twentyfive_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) :
    0 < wick 25 n - E25 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twentyfive]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_twentyfive]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_twentyfive_factored_v n
      have hstrict : (0 : ℤ) < n * 275955459042569551165547242704839136576119746893882624 := by positivity
      have h1 : (0 : ℤ) ≤ n * (760960739831712805159513442906806138387120565155152840 * (n - 8) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (1272578881276923350922927506139263845287184096090240545 * (n - 8) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (1065250257992024808380129736086886669629467089044021460 * (n - 8) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (705783916854641885947025146496925275911029660576993555 * (n - 8) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (368051189781838549250867426096933680923025228446841500 * (n - 8) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (138523500039981943279329168375799845238326463366430250 * (n - 8) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (45860027484907612427139969580797090593001765729466500 * (n - 8) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (12195152941438960477184659712783395459169184065832375 * (n - 8) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (2642472733891246244886458630030310165552658998075000 * (n - 8) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (513052627672695478153867500666666046780432562782500 * (n - 8) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (79291757660525362945268320349557483466498348085000 * (n - 8) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (10846580999894968378851902386862724579664289557500 * (n - 8) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (1274524585357430056510552592094892777652135062500 * (n - 8) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (118696563051890027875601042661589757420203500000 * (n - 8) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (10819126155501768942485797367874363072039675000 * (n - 8) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (666391577429557198123627901167432081617103125 * (n - 8) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (46591354576256319727087508224079310402890625 * (n - 8) ^ 17) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      have h18 : (0 : ℤ) ≤ n * (1804910609174240332952229015900518075859375 * (n - 8) ^ 18) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
      have h19 : (0 : ℤ) ≤ n * (94169232073940367514878288005149255781250 * (n - 8) ^ 19) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
      have h20 : (0 : ℤ) ≤ n * (2032529650068151925294235534036212203125 * (n - 8) ^ 20) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
      have h21 : (0 : ℤ) ≤ n * (76631788541524486783033951524625781250 * (n - 8) ^ 21) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
      have h22 : (0 : ℤ) ≤ n * (649611770740780507660913356975781250 * (n - 8) ^ 22) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
      have h23 : (0 : ℤ) ≤ n * (17530752433784181616036642317187500 * (n - 8) ^ 23) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 23))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]

/-- The second coefficient law at depth 25: `17530752433784181616036642317187500 = C(25,2)·49‼`. -/
theorem deficit_twentyfive_leading :
    (17530752433784181616036642317187500 : ℤ) = 300 * 58435841445947272053455474390625 := by
  norm_num

end ProximityGap.Frontier.E25ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E25ClosedForm.E25_two
#print axioms ProximityGap.Frontier.E25ClosedForm.deficit_twentyfive
#print axioms ProximityGap.Frontier.E25ClosedForm.E25_le_wick
#print axioms ProximityGap.Frontier.E25ClosedForm.deficit_twentyfive_pos
