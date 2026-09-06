/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_26(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_25`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 26`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 8`, covering the dyadic
support range `n = 2`, `n = 4`, or `n ≥ 8`. This is deliberately only a char-0 rung; it
does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E26ClosedForm

/-- `E_26(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 26`, in closed form. -/
def E26 (n : ℤ) : ℤ :=
2980227913743310874726229193921875 * n ^ 26
    - 968574071966576034286024488024609375 * n ^ 25
    + 154326135466674448129573235091921093750 * n ^ 24
    - 16009883693559524129391794104054776562500 * n ^ 23
    + 1211707502793185455858047549289395830296875 * n ^ 22
    - 71077289052073368568608173487765109184296875 * n ^ 21
    + 3351948824518322737010404101287244335519765625 * n ^ 20
    - 130148395864425133821634990626078736064106093750 * n ^ 19
    + 4227838768507002696384670105705075007585570850000 * n ^ 18
    - 116160225806447084322881908166908230064804381865625 * n ^ 17
    + 2718775259988480428466851069688710124573640720500000 * n ^ 16
    - 54444489176297182829013500816226152699221153992750000 * n ^ 15
    + 934712790953574782833944487004688651690080232368767500 * n ^ 14
    - 13757415765301792834657280176862943274537763954252415000 * n ^ 13
    + 173253076769428942043700950029160396939859650431076617500 * n ^ 12
    - 1859551703072558172928928192924445371622792503634185550000 * n ^ 11
    + 16907806788340934830756521277690210920970117126766151988875 * n ^ 10
    - 129123629614401981101740728152752948387269437786975007456375 * n ^ 9
    + 818680235779060921372943093418344838793224391133241310647750 * n ^ 8
    - 4242364465101093210231343839767473623609547285562053725705750 * n ^ 7
    + 17588548819404794473078175750924742623739456941911052541219195 * n ^ 6
    - 56631264780376784788490982997726754142545562907475918456280075 * n ^ 5
    + 135578172311959595238460159287702911058810261566398276151839125 * n ^ 4
    - 225320495396552283205852804957729411183779516616619732968921425 * n ^ 3
    + 229633084298864433167734038598315156796236410646080576741301656 * n ^ 2
    - 106624921678560642587235189194645621218854682979196318675465600 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twentysix (n : ℤ) : wick 26 n = 2980227913743310874726229193921875 * n ^ 26 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_26(2) = 495918532948104 = C(52,26)`. -/
theorem E26_two : E26 2 = 495918532948104 := by decide

/-- `E_26(4) = 245935191321399712625557194816`. -/
theorem E26_four : E26 4 = 245935191321399712625557194816 := by decide

/-! ## The exact char-0 deficit `D_26 = wick 26 n − E_26(ℂ)` -/

/-- The exact deficit `wick 26 n − E_26(ℂ)`. Its leading nonzero coefficient is
`C(26,2)·51‼ = 968574071966576034286024488024609375`. -/
theorem deficit_twentysix (n : ℤ) :
    wick 26 n - E26 n =
968574071966576034286024488024609375 * n ^ 25
    - 154326135466674448129573235091921093750 * n ^ 24
    + 16009883693559524129391794104054776562500 * n ^ 23
    - 1211707502793185455858047549289395830296875 * n ^ 22
    + 71077289052073368568608173487765109184296875 * n ^ 21
    - 3351948824518322737010404101287244335519765625 * n ^ 20
    + 130148395864425133821634990626078736064106093750 * n ^ 19
    - 4227838768507002696384670105705075007585570850000 * n ^ 18
    + 116160225806447084322881908166908230064804381865625 * n ^ 17
    - 2718775259988480428466851069688710124573640720500000 * n ^ 16
    + 54444489176297182829013500816226152699221153992750000 * n ^ 15
    - 934712790953574782833944487004688651690080232368767500 * n ^ 14
    + 13757415765301792834657280176862943274537763954252415000 * n ^ 13
    - 173253076769428942043700950029160396939859650431076617500 * n ^ 12
    + 1859551703072558172928928192924445371622792503634185550000 * n ^ 11
    - 16907806788340934830756521277690210920970117126766151988875 * n ^ 10
    + 129123629614401981101740728152752948387269437786975007456375 * n ^ 9
    - 818680235779060921372943093418344838793224391133241310647750 * n ^ 8
    + 4242364465101093210231343839767473623609547285562053725705750 * n ^ 7
    - 17588548819404794473078175750924742623739456941911052541219195 * n ^ 6
    + 56631264780376784788490982997726754142545562907475918456280075 * n ^ 5
    - 135578172311959595238460159287702911058810261566398276151839125 * n ^ 4
    + 225320495396552283205852804957729411183779516616619732968921425 * n ^ 3
    - 229633084298864433167734038598315156796236410646080576741301656 * n ^ 2
    + 106624921678560642587235189194645621218854682979196318675465600 * n ^ 1 := by
  simp only [wick_twentysix, E26]; ring

/-- `wick 26 n − E_26 = n · (Σ_k c_k · (n-8)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twentysix_factored_v (n : ℤ) :
    wick 26 n - E26 n =
      n * (      112589827289388156736351813623784853174043372578378932992
        + 453130490838862344977484171071225093242445868416362377144 * (n - 8) ^ 1
        + 400982494055718921353897525995450982561039308617087780825 * (n - 8) ^ 2
        + 546903503172445070308404448055611509287311770687785702475 * (n - 8) ^ 3
        + 362277469703114566440663912442176953205488934768108136275 * (n - 8) ^ 4
        + 166987847881041113639821470683052347893889294155515392805 * (n - 8) ^ 5
        + 81138355976540017651165551695142904510920329662086519750 * (n - 8) ^ 6
        + 25234135445944535389468679728818642523807896624336512250 * (n - 8) ^ 7
        + 7120254365712582781766888501184773060003818508917377375 * (n - 8) ^ 8
        + 1785670536212413812397817741173775421470256068508811125 * (n - 8) ^ 9
        + 327809299484136922121700417230123035314119049699210000 * (n - 8) ^ 10
        + 60053810827468729642201893466263805080771917643862500 * (n - 8) ^ 11
        + 8510066148524331679501313224686762869458657062195000 * (n - 8) ^ 12
        + 1032427571041792221074941660812451135034186883232500 * (n - 8) ^ 13
        + 121319333100815154730180948667013791513035524750000 * (n - 8) ^ 14
        + 9474978067958893472488312582597326887265783900000 * (n - 8) ^ 15
        + 917537855844024772221068930445074201710504265625 * (n - 8) ^ 16
        + 45991213765472291977735623304074079942831650000 * (n - 8) ^ 17
        + 3532755040803248667549278647176439596791718750 * (n - 8) ^ 18
        + 110122350027990976604169887632304336377734375 * (n - 8) ^ 19
        + 6421328013108391630561900450556739594421875 * (n - 8) ^ 20
        + 110904929686997272219054135061904894703125 * (n - 8) ^ 21
        + 4722767174909024743178655403607995312500 * (n - 8) ^ 22
        + 31640086350908150453343466608803906250 * (n - 8) ^ 23
        + 968574071966576034286024488024609375 * (n - 8) ^ 24) := by
  rw [deficit_twentysix]; ring_nf

/-- `0 ≤ wick 26 n − E26 n` for `n ≥ 8`, from the nonnegative `v = n−8` certificate. -/
theorem deficit_twentysix_nonneg_from_8 (n : ℤ) (hn : 8 ≤ n) :
    0 ≤ wick 26 n - E26 n := by
  have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 112589827289388156736351813623784853174043372578378932992 := by positivity
  have h1 : (0 : ℤ) ≤ n * (453130490838862344977484171071225093242445868416362377144 * (n - 8) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (400982494055718921353897525995450982561039308617087780825 * (n - 8) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (546903503172445070308404448055611509287311770687785702475 * (n - 8) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (362277469703114566440663912442176953205488934768108136275 * (n - 8) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (166987847881041113639821470683052347893889294155515392805 * (n - 8) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (81138355976540017651165551695142904510920329662086519750 * (n - 8) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (25234135445944535389468679728818642523807896624336512250 * (n - 8) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (7120254365712582781766888501184773060003818508917377375 * (n - 8) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (1785670536212413812397817741173775421470256068508811125 * (n - 8) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (327809299484136922121700417230123035314119049699210000 * (n - 8) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (60053810827468729642201893466263805080771917643862500 * (n - 8) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (8510066148524331679501313224686762869458657062195000 * (n - 8) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (1032427571041792221074941660812451135034186883232500 * (n - 8) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (121319333100815154730180948667013791513035524750000 * (n - 8) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (9474978067958893472488312582597326887265783900000 * (n - 8) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (917537855844024772221068930445074201710504265625 * (n - 8) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (45991213765472291977735623304074079942831650000 * (n - 8) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (3532755040803248667549278647176439596791718750 * (n - 8) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  have h19 : (0 : ℤ) ≤ n * (110122350027990976604169887632304336377734375 * (n - 8) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
  have h20 : (0 : ℤ) ≤ n * (6421328013108391630561900450556739594421875 * (n - 8) ^ 20) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
  have h21 : (0 : ℤ) ≤ n * (110904929686997272219054135061904894703125 * (n - 8) ^ 21) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
  have h22 : (0 : ℤ) ≤ n * (4722767174909024743178655403607995312500 * (n - 8) ^ 22) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
  have h23 : (0 : ℤ) ≤ n * (31640086350908150453343466608803906250 * (n - 8) ^ 23) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 23))
  have h24 : (0 : ℤ) ≤ n * (968574071966576034286024488024609375 * (n - 8) ^ 24) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 24))
  rw [deficit_twentysix_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]

/-- Base case `n=2`. -/
theorem E26_le_wick_base_two : E26 2 ≤ wick 26 2 := by rw [E26_two, wick_twentysix]; norm_num

/-- Base case `n=4`. -/
theorem E26_le_wick_base_four : E26 4 ≤ wick 26 4 := by rw [E26_four, wick_twentysix]; norm_num

/-- The depth-26 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem E26_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) : E26 n ≤ wick 26 n := by
  rcases hn with rfl | hrest
  · exact E26_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E26_le_wick_base_four
    · have hpos := deficit_twentysix_nonneg_from_8 n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-26 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem deficit_twentysix_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) :
    0 < wick 26 n - E26 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twentysix]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_twentysix]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_twentysix_factored_v n
      have hstrict : (0 : ℤ) < n * 112589827289388156736351813623784853174043372578378932992 := by positivity
      have h1 : (0 : ℤ) ≤ n * (453130490838862344977484171071225093242445868416362377144 * (n - 8) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (400982494055718921353897525995450982561039308617087780825 * (n - 8) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (546903503172445070308404448055611509287311770687785702475 * (n - 8) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (362277469703114566440663912442176953205488934768108136275 * (n - 8) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (166987847881041113639821470683052347893889294155515392805 * (n - 8) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (81138355976540017651165551695142904510920329662086519750 * (n - 8) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (25234135445944535389468679728818642523807896624336512250 * (n - 8) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (7120254365712582781766888501184773060003818508917377375 * (n - 8) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (1785670536212413812397817741173775421470256068508811125 * (n - 8) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (327809299484136922121700417230123035314119049699210000 * (n - 8) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (60053810827468729642201893466263805080771917643862500 * (n - 8) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (8510066148524331679501313224686762869458657062195000 * (n - 8) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (1032427571041792221074941660812451135034186883232500 * (n - 8) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (121319333100815154730180948667013791513035524750000 * (n - 8) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (9474978067958893472488312582597326887265783900000 * (n - 8) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (917537855844024772221068930445074201710504265625 * (n - 8) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (45991213765472291977735623304074079942831650000 * (n - 8) ^ 17) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      have h18 : (0 : ℤ) ≤ n * (3532755040803248667549278647176439596791718750 * (n - 8) ^ 18) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
      have h19 : (0 : ℤ) ≤ n * (110122350027990976604169887632304336377734375 * (n - 8) ^ 19) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
      have h20 : (0 : ℤ) ≤ n * (6421328013108391630561900450556739594421875 * (n - 8) ^ 20) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
      have h21 : (0 : ℤ) ≤ n * (110904929686997272219054135061904894703125 * (n - 8) ^ 21) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
      have h22 : (0 : ℤ) ≤ n * (4722767174909024743178655403607995312500 * (n - 8) ^ 22) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
      have h23 : (0 : ℤ) ≤ n * (31640086350908150453343466608803906250 * (n - 8) ^ 23) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 23))
      have h24 : (0 : ℤ) ≤ n * (968574071966576034286024488024609375 * (n - 8) ^ 24) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 24))
      rw [hcert]
      nlinarith [hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]

end ProximityGap.Frontier.E26ClosedForm

#print axioms ProximityGap.Frontier.E26ClosedForm.E26_two
#print axioms ProximityGap.Frontier.E26ClosedForm.deficit_twentysix
#print axioms ProximityGap.Frontier.E26ClosedForm.E26_le_wick
#print axioms ProximityGap.Frontier.E26ClosedForm.deficit_twentysix_pos
