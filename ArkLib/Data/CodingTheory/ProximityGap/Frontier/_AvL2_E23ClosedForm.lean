/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_23(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_22`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 23`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 7`, covering the dyadic
support range `n = 2`, `n = 4`, or `n ≥ 7`. This is deliberately only a char-0 rung; it
does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E23ClosedForm

/-- `E_23(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 23`, in closed form. -/
def E23 (n : ℤ) : ℤ :=
  25373791335626257947657609375 * n ^ 23
    - 6419569207913443260757375171875 * n ^ 22
    + 793886725378629149913662062921875 * n ^ 21
    - 63660727978474979002510637121093750 * n ^ 20
    + 3704763775847765562747848796598209375 * n ^ 19
    - 166019431431742635295220659611455081250 * n ^ 18
    + 5934832082133243922287485866208085412500 * n ^ 17
    - 173071785241785400653292589331701161312500 * n ^ 16
    + 4177108584544556887577167339584079078685625 * n ^ 15
    - 84193323422258001974378231737219246284020625 * n ^ 14
    + 1424346822282180429229882272280227175968601875 * n ^ 13
    - 20261327211525896755033888290982981992823507500 * n ^ 12
    + 242084144475454430552006254496447419573587331500 * n ^ 11
    - 2420100078033454098431664939998544136821090310875 * n ^ 10
    + 20104972292335448181631594989851091577269967171500 * n ^ 9
    - 137378260333239071917543273334939520592646140171500 * n ^ 8
    + 760922963292985825084622166392398939641665323338675 * n ^ 7
    - 3347231775153007766519663153562297907018395555317325 * n ^ 6
    + 11358425478079281810370596886933901191285805083574925 * n ^ 5
    - 28481089035017498471102872775493699383033405384953275 * n ^ 4
    + 49285087993063850724930814792302755947486578022314000 * n ^ 3
    - 52000126138960824986917431269023681180248607522228800 * n ^ 2
    + 24851181233106412668802064250521817098170742462592000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twentythree (n : ℤ) : wick 23 n = 25373791335626257947657609375 * n ^ 23 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_23(2) = 8233430727600 = C(46,23)`. -/
theorem E23_two : E23 2 = 8233430727600 := by decide

/-- `E_23(4) = 67789381546187865401760000`. -/
theorem E23_four : E23 4 = 67789381546187865401760000 := by decide

/-! ## The exact char-0 deficit `D_23 = wick 23 n − E_23(ℂ)` -/

/-- The exact deficit `wick 23 n − E_23(ℂ)`. Its leading nonzero coefficient is
`C(23,2)·45‼ = 6419569207913443260757375171875`. -/
theorem deficit_twentythree (n : ℤ) :
    wick 23 n - E23 n =
  6419569207913443260757375171875 * n ^ 22
    - 793886725378629149913662062921875 * n ^ 21
    + 63660727978474979002510637121093750 * n ^ 20
    - 3704763775847765562747848796598209375 * n ^ 19
    + 166019431431742635295220659611455081250 * n ^ 18
    - 5934832082133243922287485866208085412500 * n ^ 17
    + 173071785241785400653292589331701161312500 * n ^ 16
    - 4177108584544556887577167339584079078685625 * n ^ 15
    + 84193323422258001974378231737219246284020625 * n ^ 14
    - 1424346822282180429229882272280227175968601875 * n ^ 13
    + 20261327211525896755033888290982981992823507500 * n ^ 12
    - 242084144475454430552006254496447419573587331500 * n ^ 11
    + 2420100078033454098431664939998544136821090310875 * n ^ 10
    - 20104972292335448181631594989851091577269967171500 * n ^ 9
    + 137378260333239071917543273334939520592646140171500 * n ^ 8
    - 760922963292985825084622166392398939641665323338675 * n ^ 7
    + 3347231775153007766519663153562297907018395555317325 * n ^ 6
    - 11358425478079281810370596886933901191285805083574925 * n ^ 5
    + 28481089035017498471102872775493699383033405384953275 * n ^ 4
    - 49285087993063850724930814792302755947486578022314000 * n ^ 3
    + 52000126138960824986917431269023681180248607522228800 * n ^ 2
    - 24851181233106412668802064250521817098170742462592000 * n ^ 1 := by
  simp only [wick_twentythree, E23]; ring

/-- `wick 23 n − E_23 = n · (Σ_k c_k · (n-7)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twentythree_factored_v (n : ℤ) :
    wick 23 n - E23 n =
      n * (      182004299325563982588109728506070344941742535075
        + 206850424006106547964848588007408339506891028275 * (n - 7) ^ 1
        + 435317474322120280616486128715335222950588055950 * (n - 7) ^ 2
        + 542454019478948333933875431342383838726086728875 * (n - 7) ^ 3
        + 249023342027038825493660810626482363467201687700 * (n - 7) ^ 4
        + 165203512254167402670564852923566287344138721225 * (n - 7) ^ 5
        + 65237907847685161087761657156923054708329965450 * (n - 7) ^ 6
        + 18752776569300282498522938931614681736259116000 * (n - 7) ^ 7
        + 5983379058811634231291559711850293754026408000 * (n - 7) ^ 8
        + 1159051488386916303597858453688378137256572750 * (n - 7) ^ 9
        + 226975007820517201359477619538543700100286625 * (n - 7) ^ 10
        + 37422588021630191836592631522640659885588750 * (n - 7) ^ 11
        + 4125194857757519640731388945470734918085625 * (n - 7) ^ 12
        + 588299116598771072616101104608042694760625 * (n - 7) ^ 13
        + 37761957321974392849614099546016988064375 * (n - 7) ^ 14
        + 4365058958114948996004195013868209762500 * (n - 7) ^ 15
        + 165959077583503237362551729783785884375 * (n - 7) ^ 16
        + 14455961273192514207222769693229840625 * (n - 7) ^ 17
        + 299570908972402940014779114362259375 * (n - 7) ^ 18
        + 18573953574896229167791338830625000 * (n - 7) ^ 19
        + 149789948184647009417672087343750 * (n - 7) ^ 20
        + 6419569207913443260757375171875 * (n - 7) ^ 21) := by
  rw [deficit_twentythree]; ring_nf

/-- `0 ≤ wick 23 n − E23 n` for `n ≥ 7`, from the nonnegative `v = n−7` certificate. -/
theorem deficit_twentythree_nonneg_from_seven (n : ℤ) (hn : 7 ≤ n) :
    0 ≤ wick 23 n - E23 n := by
  have hu0 : (0 : ℤ) ≤ n - 7 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 182004299325563982588109728506070344941742535075 := by positivity
  have h1 : (0 : ℤ) ≤ n * (206850424006106547964848588007408339506891028275 * (n - 7) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (435317474322120280616486128715335222950588055950 * (n - 7) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (542454019478948333933875431342383838726086728875 * (n - 7) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (249023342027038825493660810626482363467201687700 * (n - 7) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (165203512254167402670564852923566287344138721225 * (n - 7) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (65237907847685161087761657156923054708329965450 * (n - 7) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (18752776569300282498522938931614681736259116000 * (n - 7) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (5983379058811634231291559711850293754026408000 * (n - 7) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (1159051488386916303597858453688378137256572750 * (n - 7) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (226975007820517201359477619538543700100286625 * (n - 7) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (37422588021630191836592631522640659885588750 * (n - 7) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (4125194857757519640731388945470734918085625 * (n - 7) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (588299116598771072616101104608042694760625 * (n - 7) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (37761957321974392849614099546016988064375 * (n - 7) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (4365058958114948996004195013868209762500 * (n - 7) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (165959077583503237362551729783785884375 * (n - 7) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (14455961273192514207222769693229840625 * (n - 7) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (299570908972402940014779114362259375 * (n - 7) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  have h19 : (0 : ℤ) ≤ n * (18573953574896229167791338830625000 * (n - 7) ^ 19) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
  have h20 : (0 : ℤ) ≤ n * (149789948184647009417672087343750 * (n - 7) ^ 20) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
  have h21 : (0 : ℤ) ≤ n * (6419569207913443260757375171875 * (n - 7) ^ 21) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
  rw [deficit_twentythree_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]

/-- Base case `n=2`. -/
theorem E23_le_wick_base_two : E23 2 ≤ wick 23 2 := by rw [E23_two, wick_twentythree]; norm_num

/-- Base case `n=4`. -/
theorem E23_le_wick_base_four : E23 4 ≤ wick 23 4 := by rw [E23_four, wick_twentythree]; norm_num

/-- The depth-23 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 7`. -/
theorem E23_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 7 ≤ n) : E23 n ≤ wick 23 n := by
  rcases hn with rfl | hrest
  · exact E23_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E23_le_wick_base_four
    · have hpos := deficit_twentythree_nonneg_from_seven n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-23 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 7`. -/
theorem deficit_twentythree_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 7 ≤ n) :
    0 < wick 23 n - E23 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twentythree]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_twentythree]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 7 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_twentythree_factored_v n
      have hstrict : (0 : ℤ) < n * 182004299325563982588109728506070344941742535075 := by positivity
      have h1 : (0 : ℤ) ≤ n * (206850424006106547964848588007408339506891028275 * (n - 7) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (435317474322120280616486128715335222950588055950 * (n - 7) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (542454019478948333933875431342383838726086728875 * (n - 7) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (249023342027038825493660810626482363467201687700 * (n - 7) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (165203512254167402670564852923566287344138721225 * (n - 7) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (65237907847685161087761657156923054708329965450 * (n - 7) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (18752776569300282498522938931614681736259116000 * (n - 7) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (5983379058811634231291559711850293754026408000 * (n - 7) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (1159051488386916303597858453688378137256572750 * (n - 7) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (226975007820517201359477619538543700100286625 * (n - 7) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (37422588021630191836592631522640659885588750 * (n - 7) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (4125194857757519640731388945470734918085625 * (n - 7) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (588299116598771072616101104608042694760625 * (n - 7) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (37761957321974392849614099546016988064375 * (n - 7) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (4365058958114948996004195013868209762500 * (n - 7) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (165959077583503237362551729783785884375 * (n - 7) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (14455961273192514207222769693229840625 * (n - 7) ^ 17) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      have h18 : (0 : ℤ) ≤ n * (299570908972402940014779114362259375 * (n - 7) ^ 18) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
      have h19 : (0 : ℤ) ≤ n * (18573953574896229167791338830625000 * (n - 7) ^ 19) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 19))
      have h20 : (0 : ℤ) ≤ n * (149789948184647009417672087343750 * (n - 7) ^ 20) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 20))
      have h21 : (0 : ℤ) ≤ n * (6419569207913443260757375171875 * (n - 7) ^ 21) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 21))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8,
        h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]

/-- The second coefficient law at depth 23: `6419569207913443260757375171875 = C(23,2)·45‼`. -/
theorem deficit_twentythree_leading :
    (6419569207913443260757375171875 : ℤ) = 253 * 25373791335626257947657609375 := by
  norm_num

end ProximityGap.Frontier.E23ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E23ClosedForm.E23_two
#print axioms ProximityGap.Frontier.E23ClosedForm.deficit_twentythree
#print axioms ProximityGap.Frontier.E23ClosedForm.E23_le_wick
#print axioms ProximityGap.Frontier.E23ClosedForm.deficit_twentythree_pos
