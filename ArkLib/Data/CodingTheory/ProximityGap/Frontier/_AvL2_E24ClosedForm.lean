/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_24(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_23`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 24`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 8`, covering the dyadic
support range `n = 2`, `n = 4`, or `n ≥ 8`. This is deliberately only a char-0 rung; it
does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E24ClosedForm

/-- `E_24(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 24`, in closed form. -/
def E24 (n : ℤ) : ℤ :=
  1192568192774434123539907640625 * n ^ 24
    - 329148821205743818097014508812500 * n ^ 23
    + 44453376908397956766324570606843750 * n ^ 22
    - 3898822645318903149328819692635531250 * n ^ 21
    + 248647402471667107217763071513517496875 * n ^ 20
    - 12240248046131042496653460348670418981250 * n ^ 19
    + 482070728041276373120995704425022468665625 * n ^ 18
    - 15541846422730697369404087374553343772215625 * n ^ 17
    + 416390102652038484900221783525414713469011875 * n ^ 16
    - 9361345913080408877920338153166617651625530000 * n ^ 15
    + 177651883961312737967049103757585293074548895000 * n ^ 14
    - 2853764027477924000976967326748014217344321532500 * n ^ 13
    + 38811752331620623256216136932633150890833171100500 * n ^ 12
    - 445879771339743474727137217745820459514860759102000 * n ^ 11
    + 4306339457095407677845268749737946448489022298405500 * n ^ 10
    - 34702722211180554022779178159355222991956375414139000 * n ^ 9
    + 230826477052316326689591654875848365925341722394135225 * n ^ 8
    - 1248389119915718582748590914018609937643298920565076700 * n ^ 7
    + 5376786082254149753877522522028200527366398250831316750 * n ^ 6
    - 17908274004909304134612838278830542768488819636450080100 * n ^ 5
    + 44174891247949572402997047380417284317362797376663014725 * n ^ 4
    - 75360476932401199204253617769177801939539970639890182900 * n ^ 3
    + 78548670282994532198329523366351523408510535586662587975 * n ^ 2
    - 37161698876858653417984273536968627903070713985128103000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twentyfour (n : ℤ) : wick 24 n = 1192568192774434123539907640625 * n ^ 24 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_24(2) = 32247603683100 = C(48,24)`. -/
theorem E24_two : E24 2 = 32247603683100 := by decide

/-- `E_24(4) = 1039907943302284685225610000`. -/
theorem E24_four : E24 4 = 1039907943302284685225610000 := by decide

/-! ## The exact char-0 deficit `D_24 = wick 24 n − E_24(ℂ)` -/

/-- The exact deficit `wick 24 n − E_24(ℂ)`. Its leading nonzero coefficient is
`C(24,2)·47‼ = 329148821205743818097014508812500`. -/
theorem deficit_twentyfour (n : ℤ) :
    wick 24 n - E24 n =
  329148821205743818097014508812500 * n ^ 23
    - 44453376908397956766324570606843750 * n ^ 22
    + 3898822645318903149328819692635531250 * n ^ 21
    - 248647402471667107217763071513517496875 * n ^ 20
    + 12240248046131042496653460348670418981250 * n ^ 19
    - 482070728041276373120995704425022468665625 * n ^ 18
    + 15541846422730697369404087374553343772215625 * n ^ 17
    - 416390102652038484900221783525414713469011875 * n ^ 16
    + 9361345913080408877920338153166617651625530000 * n ^ 15
    - 177651883961312737967049103757585293074548895000 * n ^ 14
    + 2853764027477924000976967326748014217344321532500 * n ^ 13
    - 38811752331620623256216136932633150890833171100500 * n ^ 12
    + 445879771339743474727137217745820459514860759102000 * n ^ 11
    - 4306339457095407677845268749737946448489022298405500 * n ^ 10
    + 34702722211180554022779178159355222991956375414139000 * n ^ 9
    - 230826477052316326689591654875848365925341722394135225 * n ^ 8
    + 1248389119915718582748590914018609937643298920565076700 * n ^ 7
    - 5376786082254149753877522522028200527366398250831316750 * n ^ 6
    + 17908274004909304134612838278830542768488819636450080100 * n ^ 5
    - 44174891247949572402997047380417284317362797376663014725 * n ^ 4
    + 75360476932401199204253617769177801939539970639890182900 * n ^ 3
    - 78548670282994532198329523366351523408510535586662587975 * n ^ 2
    + 37161698876858653417984273536968627903070713985128103000 * n ^ 1 := by
  simp only [wick_twentyfour, E24]; ring

/-- `wick 24 n − E_24 = n · (Σ_k c_k · (n-8)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twentyfour_factored_v (n : ℤ) :
    wick 24 n - E24 n =
      n * (      703968007760840982533611170776429881973391704128800
        + 2072104688414705652570386104555001210104001236032825 * (n - 8) ^ 1
        + 2724341285361652200276581307813365071861672236479100 * (n - 8) ^ 2
        + 2452356898296787395907373940791466190278496538684475 * (n - 8) ^ 3
        + 1529514943140353385662327189227206745726814145986100 * (n - 8) ^ 4
        + 715755144078303374028863622940324684743209809950450 * (n - 8) ^ 5
        + 273226938808775962929985455141187564704429634880100 * (n - 8) ^ 6
        + 82107934500135003724652836545184399495301832488775 * (n - 8) ^ 7
        + 20498670551151240062320331141662557221387880303000 * (n - 8) ^ 8
        + 4317766825997863332071045984628992077070646874500 * (n - 8) ^ 9
        + 744212955889730633101028190216481563578455218000 * (n - 8) ^ 10
        + 111331820275065449740540745465586604910832019500 * (n - 8) ^ 11
        + 13871620837668657531366270932329279392555172500 * (n - 8) ^ 12
        + 1449686144626789765658013441004883036633865000 * (n - 8) ^ 13
        + 133647294508798692580150322383875311995305000 * (n - 8) ^ 14
        + 9462736878268801284971054366696331824188125 * (n - 8) ^ 15
        + 645002792498951117018728772370329656490625 * (n - 8) ^ 16
        + 29264280276357367083245193221222250834375 * (n - 8) ^ 17
        + 1446590674656417512134633337149739456250 * (n - 8) ^ 18
        + 37238097674793743428579850260667503125 * (n - 8) ^ 19
        + 1296791497413763019332554328969781250 * (n - 8) ^ 20
        + 13476815623812955218749982944156250 * (n - 8) ^ 21
        + 329148821205743818097014508812500 * (n - 8) ^ 22) := by
  rw [deficit_twentyfour]; ring_nf

/-- `0 ≤ wick 24 n − E24 n` for `n ≥ 8`, from the nonnegative `v = n−8` certificate. -/
theorem deficit_twentyfour_nonneg_from_eight (n : ℤ) (hn : 8 ≤ n) :
    0 ≤ wick 24 n - E24 n := by
  have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 703968007760840982533611170776429881973391704128800 := by positivity
  have h1 : (0 : ℤ) ≤ n * (2072104688414705652570386104555001210104001236032825 * (n - 8) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (2724341285361652200276581307813365071861672236479100 * (n - 8) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (2452356898296787395907373940791466190278496538684475 * (n - 8) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (1529514943140353385662327189227206745726814145986100 * (n - 8) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (715755144078303374028863622940324684743209809950450 * (n - 8) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (273226938808775962929985455141187564704429634880100 * (n - 8) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (82107934500135003724652836545184399495301832488775 * (n - 8) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (20498670551151240062320331141662557221387880303000 * (n - 8) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (4317766825997863332071045984628992077070646874500 * (n - 8) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (744212955889730633101028190216481563578455218000 * (n - 8) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (111331820275065449740540745465586604910832019500 * (n - 8) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (13871620837668657531366270932329279392555172500 * (n - 8) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (1449686144626789765658013441004883036633865000 * (n - 8) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (133647294508798692580150322383875311995305000 * (n - 8) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (9462736878268801284971054366696331824188125 * (n - 8) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (645002792498951117018728772370329656490625 * (n - 8) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (29264280276357367083245193221222250834375 * (n - 8) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (1446590674656417512134633337149739456250 * (n - 8) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  have h19 : (0 : ℤ) ≤ n * (37238097674793743428579850260667503125 * (n - 8) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
  have h20 : (0 : ℤ) ≤ n * (1296791497413763019332554328969781250 * (n - 8) ^ 20) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
  have h21 : (0 : ℤ) ≤ n * (13476815623812955218749982944156250 * (n - 8) ^ 21) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
  have h22 : (0 : ℤ) ≤ n * (329148821205743818097014508812500 * (n - 8) ^ 22) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
  rw [deficit_twentyfour_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]

/-- Base case `n=2`. -/
theorem E24_le_wick_base_two : E24 2 ≤ wick 24 2 := by rw [E24_two, wick_twentyfour]; norm_num

/-- Base case `n=4`. -/
theorem E24_le_wick_base_four : E24 4 ≤ wick 24 4 := by rw [E24_four, wick_twentyfour]; norm_num

/-- The depth-24 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem E24_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) : E24 n ≤ wick 24 n := by
  rcases hn with rfl | hrest
  · exact E24_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E24_le_wick_base_four
    · have hpos := deficit_twentyfour_nonneg_from_eight n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-24 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 8`. -/
theorem deficit_twentyfour_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 8 ≤ n) :
    0 < wick 24 n - E24 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twentyfour]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_twentyfour]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 8 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_twentyfour_factored_v n
      have hstrict : (0 : ℤ) < n * 703968007760840982533611170776429881973391704128800 := by positivity
      have h1 : (0 : ℤ) ≤ n * (2072104688414705652570386104555001210104001236032825 * (n - 8) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (2724341285361652200276581307813365071861672236479100 * (n - 8) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (2452356898296787395907373940791466190278496538684475 * (n - 8) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (1529514943140353385662327189227206745726814145986100 * (n - 8) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (715755144078303374028863622940324684743209809950450 * (n - 8) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (273226938808775962929985455141187564704429634880100 * (n - 8) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (82107934500135003724652836545184399495301832488775 * (n - 8) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (20498670551151240062320331141662557221387880303000 * (n - 8) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (4317766825997863332071045984628992077070646874500 * (n - 8) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (744212955889730633101028190216481563578455218000 * (n - 8) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (111331820275065449740540745465586604910832019500 * (n - 8) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (13871620837668657531366270932329279392555172500 * (n - 8) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (1449686144626789765658013441004883036633865000 * (n - 8) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (133647294508798692580150322383875311995305000 * (n - 8) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (9462736878268801284971054366696331824188125 * (n - 8) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (645002792498951117018728772370329656490625 * (n - 8) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (29264280276357367083245193221222250834375 * (n - 8) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      have h18 : (0 : ℤ) ≤ n * (1446590674656417512134633337149739456250 * (n - 8) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
      have h19 : (0 : ℤ) ≤ n * (37238097674793743428579850260667503125 * (n - 8) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
      have h20 : (0 : ℤ) ≤ n * (1296791497413763019332554328969781250 * (n - 8) ^ 20) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
      have h21 : (0 : ℤ) ≤ n * (13476815623812955218749982944156250 * (n - 8) ^ 21) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
      have h22 : (0 : ℤ) ≤ n * (329148821205743818097014508812500 * (n - 8) ^ 22) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]

/-- The second coefficient law at depth 24: `329148821205743818097014508812500 = C(24,2)·47‼`. -/
theorem deficit_twentyfour_leading :
    (329148821205743818097014508812500 : ℤ) = 276 * 1192568192774434123539907640625 := by
  norm_num

end ProximityGap.Frontier.E24ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E24ClosedForm.E24_two
#print axioms ProximityGap.Frontier.E24ClosedForm.deficit_twentyfour
#print axioms ProximityGap.Frontier.E24ClosedForm.E24_le_wick
#print axioms ProximityGap.Frontier.E24ClosedForm.deficit_twentyfour_pos
