/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_27(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_26`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 27`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 9`, with `n = 2`, `n = 4`,
and `n = 8` checked separately, covering the dyadic support range. This is deliberately only
a char-0 rung; it does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E27ClosedForm

/-- `E_27(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 27`, in closed form. -/
def E27 (n : ℤ) : ℤ :=
157952079428395476360490147277859375 * n ^ 27
    - 55441179879366812202532041694528640625 * n ^ 26
    + 9548203201446506545991629402946599218750 * n ^ 25
    - 1071862811001091702582286139427553718750000 * n ^ 24
    + 87909163144710844757300605603772900027296875 * n ^ 23
    - 5597634338345848817209135584173750997045890625 * n ^ 22
    + 287146974709807333871106445442763354460280390625 * n ^ 21
    - 12157110241034179034648380212442037878711607812500 * n ^ 20
    + 431834553676948839202631243176826820142876900143750 * n ^ 19
    - 13016026743265819024318394188967218106998867322334375 * n ^ 18
    + 335466542874651434583059622143732268432273675478425000 * n ^ 17
    - 7429682109635383304636221130475709167999607726897875000 * n ^ 16
    + 141780768038958083312846235109165711015317212135690977500 * n ^ 15
    - 2333115547150218721428306895811373570896594939741366985000 * n ^ 14
    + 33075762226646014945460121740305955939354686545462126097500 * n ^ 13
    - 402876051254612238285465006469777902390513287108346171840000 * n ^ 12
    + 4197278354019437038249918959007597495825482984287825091570375 * n ^ 11
    - 37159231757982723026925041642146936963800066669980597896787625 * n ^ 10
    + 277073151080762630322884184186863123293421557975026957810666750 * n ^ 9
    - 1719376218979623969574612053503380818772598891333749476765329250 * n ^ 8
    + 8739477713657056140861157464583364609403413334941069526112030335 * n ^ 7
    - 35612039803648290091155180429865949467255762450687841097527123685 * n ^ 6
    + 112905433705057228806407247532273491335201104910367413630797812225 * n ^ 5
    - 266620689310546006406406242372639693013137315934904485993984254775 * n ^ 4
    + 437797587117146090125428451151715995333403178991205097576412544768 * n ^ 3
    - 441559803675302368122124149570921131188531130067584766872590795968 * n ^ 2
    + 203250101953408095034567613795638740418479858086700561224543872000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twentyseven (n : ℤ) : wick 27 n = 157952079428395476360490147277859375 * n ^ 27 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_27(2) = 1946939425648112 = C(54,27)`. -/
theorem E27_two : E27 2 = 1946939425648112 := by decide

/-- `E_27(4) = 3790573127143000234651249164544`. -/
theorem E27_four : E27 4 = 3790573127143000234651249164544 := by decide

/-- `E_27(8) = 1595507883441056800836236333149791985348050944`. -/
theorem E27_eight : E27 8 = 1595507883441056800836236333149791985348050944 := by decide

/-! ## The exact char-0 deficit `D_27 = wick 27 n − E_27(ℂ)` -/

/-- The exact deficit `wick 27 n − E_27(ℂ)`. Its leading nonzero coefficient is
`C(27,2)·53‼ = 55441179879366812202532041694528640625`. -/
theorem deficit_twentyseven (n : ℤ) :
    wick 27 n - E27 n =
55441179879366812202532041694528640625 * n ^ 26
    - 9548203201446506545991629402946599218750 * n ^ 25
    + 1071862811001091702582286139427553718750000 * n ^ 24
    - 87909163144710844757300605603772900027296875 * n ^ 23
    + 5597634338345848817209135584173750997045890625 * n ^ 22
    - 287146974709807333871106445442763354460280390625 * n ^ 21
    + 12157110241034179034648380212442037878711607812500 * n ^ 20
    - 431834553676948839202631243176826820142876900143750 * n ^ 19
    + 13016026743265819024318394188967218106998867322334375 * n ^ 18
    - 335466542874651434583059622143732268432273675478425000 * n ^ 17
    + 7429682109635383304636221130475709167999607726897875000 * n ^ 16
    - 141780768038958083312846235109165711015317212135690977500 * n ^ 15
    + 2333115547150218721428306895811373570896594939741366985000 * n ^ 14
    - 33075762226646014945460121740305955939354686545462126097500 * n ^ 13
    + 402876051254612238285465006469777902390513287108346171840000 * n ^ 12
    - 4197278354019437038249918959007597495825482984287825091570375 * n ^ 11
    + 37159231757982723026925041642146936963800066669980597896787625 * n ^ 10
    - 277073151080762630322884184186863123293421557975026957810666750 * n ^ 9
    + 1719376218979623969574612053503380818772598891333749476765329250 * n ^ 8
    - 8739477713657056140861157464583364609403413334941069526112030335 * n ^ 7
    + 35612039803648290091155180429865949467255762450687841097527123685 * n ^ 6
    - 112905433705057228806407247532273491335201104910367413630797812225 * n ^ 5
    + 266620689310546006406406242372639693013137315934904485993984254775 * n ^ 4
    - 437797587117146090125428451151715995333403178991205097576412544768 * n ^ 3
    + 441559803675302368122124149570921131188531130067584766872590795968 * n ^ 2
    - 203250101953408095034567613795638740418479858086700561224543872000 * n ^ 1 := by
  simp only [wick_twentyseven, E27]; ring

/-- `wick 27 n − E_27 = n · (Σ_k c_k · (n-9)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twentyseven_factored_v (n : ℤ) :
    wick 27 n - E27 n =
      n * (      989751617590123428753323580271042772083839980627884032198959
        + 2985366342860986478275047867928363472071929532581886004378304 * (n - 9) ^ 1
        + 4109446917741547848218594921045824209646641418987060704123432 * (n - 9) ^ 2
        + 3604115857947249079490025981958808885464371305725934161303725 * (n - 9) ^ 3
        + 2342919742342653374331409529534416991800819380017974546918950 * (n - 9) ^ 4
        + 1134754492527824659268910664875027022632493148858577631773720 * (n - 9) ^ 5
        + 440855818469206795134123535487639503554085696637688796739790 * (n - 9) ^ 6
        + 141006064007061548868671277664453224830427933961664237705250 * (n - 9) ^ 7
        + 36905508800565657318556607870272719694565107992509807377125 * (n - 9) ^ 8
        + 8237732719914100651523183897021980571544574983397762943250 * (n - 9) ^ 9
        + 1557924049627569951531680870734686744979644551191827498375 * (n - 9) ^ 10
        + 250235379101783970003124362401841894931375441708506187500 * (n - 9) ^ 11
        + 35052378149290110176025157540912907081564758186460463750 * (n - 9) ^ 12
        + 4163863762873719119607751287464841714434455619002563750 * (n - 9) ^ 13
        + 430533889048827897810866472114635548293703086536553750 * (n - 9) ^ 14
        + 38529942624748066963848576572887827654396738132450000 * (n - 9) ^ 15
        + 2886501768005398288845925738474828065537088122646875 * (n - 9) ^ 16
        + 195481149339958142643145380441152332470226425890625 * (n - 9) ^ 17
        + 10264736697140017927454604071345375720090391028125 * (n - 9) ^ 18
        + 520794802272323701861456966532907196086794531250 * (n - 9) ^ 19
        + 18035971221007675239431148848756301280361578125 * (n - 9) ^ 20
        + 670401192651808727687221290691680290045015625 * (n - 9) ^ 21
        + 13465034264711371355029232634672719355515625 * (n - 9) ^ 22
        + 356671590557259825169622801568134254687500 * (n - 9) ^ 23
        + 2926062271411026199578079978322344921875 * (n - 9) ^ 24
        + 55441179879366812202532041694528640625 * (n - 9) ^ 25) := by
  rw [deficit_twentyseven]; ring_nf

/-- `0 ≤ wick 27 n − E27 n` for `n ≥ 9`, from the nonnegative `v = n−9` certificate. -/
theorem deficit_twentyseven_nonneg_from_9 (n : ℤ) (hn : 9 ≤ n) :
    0 ≤ wick 27 n - E27 n := by
  have hu0 : (0 : ℤ) ≤ n - 9 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 989751617590123428753323580271042772083839980627884032198959 := by positivity
  have h1 : (0 : ℤ) ≤ n * (2985366342860986478275047867928363472071929532581886004378304 * (n - 9) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (4109446917741547848218594921045824209646641418987060704123432 * (n - 9) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (3604115857947249079490025981958808885464371305725934161303725 * (n - 9) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (2342919742342653374331409529534416991800819380017974546918950 * (n - 9) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (1134754492527824659268910664875027022632493148858577631773720 * (n - 9) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (440855818469206795134123535487639503554085696637688796739790 * (n - 9) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (141006064007061548868671277664453224830427933961664237705250 * (n - 9) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (36905508800565657318556607870272719694565107992509807377125 * (n - 9) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (8237732719914100651523183897021980571544574983397762943250 * (n - 9) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (1557924049627569951531680870734686744979644551191827498375 * (n - 9) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (250235379101783970003124362401841894931375441708506187500 * (n - 9) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (35052378149290110176025157540912907081564758186460463750 * (n - 9) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (4163863762873719119607751287464841714434455619002563750 * (n - 9) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (430533889048827897810866472114635548293703086536553750 * (n - 9) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (38529942624748066963848576572887827654396738132450000 * (n - 9) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (2886501768005398288845925738474828065537088122646875 * (n - 9) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (195481149339958142643145380441152332470226425890625 * (n - 9) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (10264736697140017927454604071345375720090391028125 * (n - 9) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  have h19 : (0 : ℤ) ≤ n * (520794802272323701861456966532907196086794531250 * (n - 9) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
  have h20 : (0 : ℤ) ≤ n * (18035971221007675239431148848756301280361578125 * (n - 9) ^ 20) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
  have h21 : (0 : ℤ) ≤ n * (670401192651808727687221290691680290045015625 * (n - 9) ^ 21) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
  have h22 : (0 : ℤ) ≤ n * (13465034264711371355029232634672719355515625 * (n - 9) ^ 22) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
  have h23 : (0 : ℤ) ≤ n * (356671590557259825169622801568134254687500 * (n - 9) ^ 23) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 23))
  have h24 : (0 : ℤ) ≤ n * (2926062271411026199578079978322344921875 * (n - 9) ^ 24) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 24))
  have h25 : (0 : ℤ) ≤ n * (55441179879366812202532041694528640625 * (n - 9) ^ 25) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 25))
  rw [deficit_twentyseven_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]

/-- Base case `n=2`. -/
theorem E27_le_wick_base_two : E27 2 ≤ wick 27 2 := by rw [E27_two, wick_twentyseven]; norm_num

/-- Base case `n=4`. -/
theorem E27_le_wick_base_four : E27 4 ≤ wick 27 4 := by rw [E27_four, wick_twentyseven]; norm_num

/-- Base case `n=8`. -/
theorem E27_le_wick_base_eight : E27 8 ≤ wick 27 8 := by rw [E27_eight, wick_twentyseven]; norm_num

/-- The depth-27 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, `n = 8`, or `n ≥ 9`. -/
theorem E27_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ 9 ≤ n) : E27 n ≤ wick 27 n := by
  rcases hn with rfl | hrest
  · exact E27_le_wick_base_two
  · rcases hrest with rfl | hrest
    · exact E27_le_wick_base_four
    · rcases hrest with rfl | hge
      · exact E27_le_wick_base_eight
      · have hpos := deficit_twentyseven_nonneg_from_9 n hge
        linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-27 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, `n = 8`, or `n ≥ 9`. -/
theorem deficit_twentyseven_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ 9 ≤ n) :
    0 < wick 27 n - E27 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twentyseven]; norm_num
  · rcases hrest with rfl | hrest
    · rw [deficit_twentyseven]; norm_num
    · rcases hrest with rfl | hge
      · rw [deficit_twentyseven]; norm_num
      · have hu0 : (0 : ℤ) ≤ n - 9 := by linarith
        have hn0 : (0 : ℤ) ≤ n := by linarith
        have hcert := deficit_twentyseven_factored_v n
        have hstrict : (0 : ℤ) < n * 989751617590123428753323580271042772083839980627884032198959 := by positivity
        have h1 : (0 : ℤ) ≤ n * (2985366342860986478275047867928363472071929532581886004378304 * (n - 9) ^ 1) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
        have h2 : (0 : ℤ) ≤ n * (4109446917741547848218594921045824209646641418987060704123432 * (n - 9) ^ 2) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
        have h3 : (0 : ℤ) ≤ n * (3604115857947249079490025981958808885464371305725934161303725 * (n - 9) ^ 3) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
        have h4 : (0 : ℤ) ≤ n * (2342919742342653374331409529534416991800819380017974546918950 * (n - 9) ^ 4) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
        have h5 : (0 : ℤ) ≤ n * (1134754492527824659268910664875027022632493148858577631773720 * (n - 9) ^ 5) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
        have h6 : (0 : ℤ) ≤ n * (440855818469206795134123535487639503554085696637688796739790 * (n - 9) ^ 6) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
        have h7 : (0 : ℤ) ≤ n * (141006064007061548868671277664453224830427933961664237705250 * (n - 9) ^ 7) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
        have h8 : (0 : ℤ) ≤ n * (36905508800565657318556607870272719694565107992509807377125 * (n - 9) ^ 8) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
        have h9 : (0 : ℤ) ≤ n * (8237732719914100651523183897021980571544574983397762943250 * (n - 9) ^ 9) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
        have h10 : (0 : ℤ) ≤ n * (1557924049627569951531680870734686744979644551191827498375 * (n - 9) ^ 10) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
        have h11 : (0 : ℤ) ≤ n * (250235379101783970003124362401841894931375441708506187500 * (n - 9) ^ 11) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
        have h12 : (0 : ℤ) ≤ n * (35052378149290110176025157540912907081564758186460463750 * (n - 9) ^ 12) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
        have h13 : (0 : ℤ) ≤ n * (4163863762873719119607751287464841714434455619002563750 * (n - 9) ^ 13) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
        have h14 : (0 : ℤ) ≤ n * (430533889048827897810866472114635548293703086536553750 * (n - 9) ^ 14) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
        have h15 : (0 : ℤ) ≤ n * (38529942624748066963848576572887827654396738132450000 * (n - 9) ^ 15) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
        have h16 : (0 : ℤ) ≤ n * (2886501768005398288845925738474828065537088122646875 * (n - 9) ^ 16) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
        have h17 : (0 : ℤ) ≤ n * (195481149339958142643145380441152332470226425890625 * (n - 9) ^ 17) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
        have h18 : (0 : ℤ) ≤ n * (10264736697140017927454604071345375720090391028125 * (n - 9) ^ 18) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
        have h19 : (0 : ℤ) ≤ n * (520794802272323701861456966532907196086794531250 * (n - 9) ^ 19) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
        have h20 : (0 : ℤ) ≤ n * (18035971221007675239431148848756301280361578125 * (n - 9) ^ 20) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
        have h21 : (0 : ℤ) ≤ n * (670401192651808727687221290691680290045015625 * (n - 9) ^ 21) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
        have h22 : (0 : ℤ) ≤ n * (13465034264711371355029232634672719355515625 * (n - 9) ^ 22) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 22))
        have h23 : (0 : ℤ) ≤ n * (356671590557259825169622801568134254687500 * (n - 9) ^ 23) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 23))
        have h24 : (0 : ℤ) ≤ n * (2926062271411026199578079978322344921875 * (n - 9) ^ 24) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 24))
        have h25 : (0 : ℤ) ≤ n * (55441179879366812202532041694528640625 * (n - 9) ^ 25) :=
          mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 25))
        rw [hcert]
        nlinarith [hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]

end ProximityGap.Frontier.E27ClosedForm

#print axioms ProximityGap.Frontier.E27ClosedForm.E27_two
#print axioms ProximityGap.Frontier.E27ClosedForm.deficit_twentyseven
#print axioms ProximityGap.Frontier.E27ClosedForm.E27_le_wick
#print axioms ProximityGap.Frontier.E27ClosedForm.deficit_twentyseven_pos
