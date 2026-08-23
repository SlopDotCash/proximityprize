/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch
import ArkLib.Data.CodingTheory.ProximityGap.StaircaseBandTheorem
import Mathlib.NumberTheory.LucasPrimality

/-!
# The μ = 6 conditional literal-budget pin: one named divisibility hypothesis (#371)

`Mu6LiteralBands.lean` certified all twelve `μ = 6` literal-budget bands open; the only
missing piece for `n = 64` pins at `ε* = 2⁻¹²⁸` is the bad side, whose in-tree size
threshold `2¹⁹² < p` overshoots every band.  **This file wires the divisibility route**
(`kkh26_epsMCA_lower_bound_of_not_dvd`, hypotheses: `2^μ < p` + `p` divides no collision
resultant) through the interior-ceiling consumer and the ceiling-march good side, and
instantiates it at a certified Proth prime inside the `r = 5` band:

> **`deltaStar_pin_mu6_dim4_of_not_dvd`** — given only the named in-tree hypothesis
> `p ∤ collisionResultant 6 d₁ d₂` (for the `sigData (2⁵) 5` signed pairs),
> `mcaDeltaStar(evalCode g 64 3, 1/2¹²⁸) = 59/64` — the dimension-4 (rate `4/64`) code
> on the 64-point smooth domain, beyond Johnson (`3/4 < 59/64 < 60/64` = capacity).

`P = 1526377·2¹²⁸ + 1 ≈ 2^{148.5}` is certified prime here (Lucas, literal squaring
chains as in `CertifiedRungPrime.lean`); the order-64 element is the chain value
`g = 3^((P−1)/64) = u₁₂₂`.  The divisibility hypothesis is exactly what the Landau
ℓ²-sharpening of `natAbs_resultant_cyclotomic_le` discharges for ALL `p > 2^{127.5}`
(see `cyclotomicLandauSqBound_proved` in `KKH26SumsOfRootsOfUnity.lean`), and what the
[TZ24] good-prime supply discharges for `p = Θ(n^β)`: either route closes this pin with no
further work on this file.  The theorem `deltaStar_pin_mu6_dim4` applies the proved
Parseval + AM-GM cyclotomic Landau bound to remove the last named analytic assumption.

**General wiring** (reusable at every `(μ, r)`):
`kkh26_deltaStar_pin_of_interior_ceiling_of_not_dvd` (the divisibility twin of the
reduction consumer) and `kkh26_march_deltaStar_pin_of_not_dvd`
(the ceiling-march pin under the divisibility hypothesis — the good side never needed a
`p`-threshold).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ProximityGap.StaircaseBandTheorem

namespace ArkLib.ProximityGap.Mu6ConditionalPin

/-! ## General wiring: the divisibility-route pin consumers -/

/-- The divisibility twin of `kkh26_deltaStar_pin_of_interior_ceiling`: same conclusion,
with the size threshold replaced by `2^μ < p` plus the collision-resultant hypothesis. -/
theorem kkh26_deltaStar_pin_of_interior_ceiling_of_not_dvd
    {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hpl : (2 : ℕ) ^ μ < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂)
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    (hceiling : InteriorCeiling p n g μ m r εstar) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hbad_at : εstar < epsMCA (F := ZMod p) (A := ZMod p)
      (evalCode g n ((r - 2) * m)) (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) :=
    lt_of_lt_of_le hεstar
      (kkh26_epsMCA_lower_bound_of_not_dvd hμ hm hn hg hpl hr2 hr hndvd)
  exact mcaDeltaStar_eq_of_good_below_of_bad_above
    (evalCode g n ((r - 2) * m)) εstar tsub_le_self hceiling
    (fun δ hδ => lt_of_lt_of_le hbad_at
      (epsMCA_mono (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) hδ))

/-- The ceiling-march pin under the divisibility hypothesis (`m = 1`): the good side
(`interiorCeiling_march`) never needed a `p`-threshold, so the whole pin transfers. -/
theorem kkh26_march_deltaStar_pin_of_not_dvd {p : ℕ} [Fact p.Prime] {μ r : ℕ}
    (hμ : 1 ≤ μ) (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) {n : ℕ} (hn : n = 2 ^ μ)
    [NeZero n] {g : ZMod p} (hg : orderOf g = 2 ^ μ) (hpl : (2 : ℕ) ^ μ < p)
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂)
    (εstar : ℝ≥0∞)
    (hlo : ((n.choose r / r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (r - 2)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hgn : orderOf g = n := by rw [hn]; exact hg
  have h := kkh26_deltaStar_pin_of_interior_ceiling_of_not_dvd (p := p) (n := n)
    (μ := μ) (m := 1) (r := r) (g := g) hμ le_rfl (by rw [hn, mul_one])
    (by rw [mul_one]; exact hg) hpl hr2 hr hndvd εstar hhi
    (ArkLib.ProximityGap.KKH26CeilingMarch.interiorCeiling_march hr2 hn hgn εstar hlo)
  rwa [mul_one] at h

/-! ## The certified prime `P = 1526377·2¹²⁸ + 1` -/

abbrev P : ℕ := 519399178373681289045835343167880067297574913

private theorem pow_two_pow_succ {M : Type} [Monoid M] (a : M) (k : ℕ) :
    a ^ (2:ℕ) ^ (k + 1) = (a ^ (2:ℕ) ^ k) ^ 2 := by
  rw [← pow_mul]
  congr 1

private theorem t0 : (3 : ZMod P) ^ (2:ℕ) ^ 0 = 3 := by norm_num
private theorem t1 :
    (3 : ZMod P) ^ (2:ℕ) ^ 1 =
      9 := by
  rw [pow_two_pow_succ, t0]; decide
private theorem t2 :
    (3 : ZMod P) ^ (2:ℕ) ^ 2 =
      81 := by
  rw [pow_two_pow_succ, t1]; decide
private theorem t3 :
    (3 : ZMod P) ^ (2:ℕ) ^ 3 =
      6561 := by
  rw [pow_two_pow_succ, t2]; decide
private theorem t4 :
    (3 : ZMod P) ^ (2:ℕ) ^ 4 =
      43046721 := by
  rw [pow_two_pow_succ, t3]; decide
private theorem t5 :
    (3 : ZMod P) ^ (2:ℕ) ^ 5 =
      1853020188851841 := by
  rw [pow_two_pow_succ, t4]; decide
private theorem t6 :
    (3 : ZMod P) ^ (2:ℕ) ^ 6 =
      3433683820292512484657849089281 := by
  rw [pow_two_pow_succ, t5]; decide
private theorem t7 :
    (3 : ZMod P) ^ (2:ℕ) ^ 7 =
      228065712611034509944143765974031586119347706 := by
  rw [pow_two_pow_succ, t6]; decide
private theorem t8 :
    (3 : ZMod P) ^ (2:ℕ) ^ 8 =
      43072187466856469685885450813561973523739483 := by
  rw [pow_two_pow_succ, t7]; decide
private theorem t9 :
    (3 : ZMod P) ^ (2:ℕ) ^ 9 =
      497852135667094781539109168323553992149089065 := by
  rw [pow_two_pow_succ, t8]; decide
private theorem t10 :
    (3 : ZMod P) ^ (2:ℕ) ^ 10 =
      20403845901268930980234355816296923623175047 := by
  rw [pow_two_pow_succ, t9]; decide
private theorem t11 :
    (3 : ZMod P) ^ (2:ℕ) ^ 11 =
      255666480431108501129978936763884898126111383 := by
  rw [pow_two_pow_succ, t10]; decide
private theorem t12 :
    (3 : ZMod P) ^ (2:ℕ) ^ 12 =
      449182501477624682966126470759939013803914115 := by
  rw [pow_two_pow_succ, t11]; decide
private theorem t13 :
    (3 : ZMod P) ^ (2:ℕ) ^ 13 =
      112758051546998851526865407038977059203320907 := by
  rw [pow_two_pow_succ, t12]; decide
private theorem t14 :
    (3 : ZMod P) ^ (2:ℕ) ^ 14 =
      160428318567654354820952954514799341508487666 := by
  rw [pow_two_pow_succ, t13]; decide
private theorem t15 :
    (3 : ZMod P) ^ (2:ℕ) ^ 15 =
      359423033303286080511399275780196807204769211 := by
  rw [pow_two_pow_succ, t14]; decide
private theorem t16 :
    (3 : ZMod P) ^ (2:ℕ) ^ 16 =
      511355497069495878322894432993965136216014421 := by
  rw [pow_two_pow_succ, t15]; decide
private theorem t17 :
    (3 : ZMod P) ^ (2:ℕ) ^ 17 =
      205052119606516883777540911302034286084892864 := by
  rw [pow_two_pow_succ, t16]; decide
private theorem t18 :
    (3 : ZMod P) ^ (2:ℕ) ^ 18 =
      194817614786876386444132326722148548494134323 := by
  rw [pow_two_pow_succ, t17]; decide
private theorem t19 :
    (3 : ZMod P) ^ (2:ℕ) ^ 19 =
      192941453596596735645891842492554496035260606 := by
  rw [pow_two_pow_succ, t18]; decide
private theorem t20 :
    (3 : ZMod P) ^ (2:ℕ) ^ 20 =
      484267760086429855812755867269001711831712636 := by
  rw [pow_two_pow_succ, t19]; decide
private theorem t21 :
    (3 : ZMod P) ^ (2:ℕ) ^ 21 =
      727578933255653090878309823080477899700738 := by
  rw [pow_two_pow_succ, t20]; decide
private theorem t22 :
    (3 : ZMod P) ^ (2:ℕ) ^ 22 =
      140694317764393925153748869543851090171965802 := by
  rw [pow_two_pow_succ, t21]; decide
private theorem t23 :
    (3 : ZMod P) ^ (2:ℕ) ^ 23 =
      234510658662045429773243596360695919519608027 := by
  rw [pow_two_pow_succ, t22]; decide
private theorem t24 :
    (3 : ZMod P) ^ (2:ℕ) ^ 24 =
      241607900442948720040330515480301420026300289 := by
  rw [pow_two_pow_succ, t23]; decide
private theorem t25 :
    (3 : ZMod P) ^ (2:ℕ) ^ 25 =
      292891020054081936178619450720223551144353092 := by
  rw [pow_two_pow_succ, t24]; decide
private theorem t26 :
    (3 : ZMod P) ^ (2:ℕ) ^ 26 =
      4996044051969701795770268772251796736204598 := by
  rw [pow_two_pow_succ, t25]; decide
private theorem t27 :
    (3 : ZMod P) ^ (2:ℕ) ^ 27 =
      183402437906963696438055394888422903800916339 := by
  rw [pow_two_pow_succ, t26]; decide
private theorem t28 :
    (3 : ZMod P) ^ (2:ℕ) ^ 28 =
      116518664219697697342662224764410173472276610 := by
  rw [pow_two_pow_succ, t27]; decide
private theorem t29 :
    (3 : ZMod P) ^ (2:ℕ) ^ 29 =
      220893895515778481797020545041457011324216489 := by
  rw [pow_two_pow_succ, t28]; decide
private theorem t30 :
    (3 : ZMod P) ^ (2:ℕ) ^ 30 =
      516826235946465472299890257827866643061655308 := by
  rw [pow_two_pow_succ, t29]; decide
private theorem t31 :
    (3 : ZMod P) ^ (2:ℕ) ^ 31 =
      297905214550814842739517111579678471298489550 := by
  rw [pow_two_pow_succ, t30]; decide
private theorem t32 :
    (3 : ZMod P) ^ (2:ℕ) ^ 32 =
      365263320481666447009561775327697273987548282 := by
  rw [pow_two_pow_succ, t31]; decide
private theorem t33 :
    (3 : ZMod P) ^ (2:ℕ) ^ 33 =
      175908287053822225476825772727444905204042458 := by
  rw [pow_two_pow_succ, t32]; decide
private theorem t34 :
    (3 : ZMod P) ^ (2:ℕ) ^ 34 =
      382899696464088930134018725868951985338062906 := by
  rw [pow_two_pow_succ, t33]; decide
private theorem t35 :
    (3 : ZMod P) ^ (2:ℕ) ^ 35 =
      56595227915738547726825161930673366742102267 := by
  rw [pow_two_pow_succ, t34]; decide
private theorem t36 :
    (3 : ZMod P) ^ (2:ℕ) ^ 36 =
      215467256016008595706071912327616731392984047 := by
  rw [pow_two_pow_succ, t35]; decide
private theorem t37 :
    (3 : ZMod P) ^ (2:ℕ) ^ 37 =
      155957241897059313148664803990722653418482562 := by
  rw [pow_two_pow_succ, t36]; decide
private theorem t38 :
    (3 : ZMod P) ^ (2:ℕ) ^ 38 =
      217705418891161451419933000669079367556377392 := by
  rw [pow_two_pow_succ, t37]; decide
private theorem t39 :
    (3 : ZMod P) ^ (2:ℕ) ^ 39 =
      121192418854032953872221156822150302796329735 := by
  rw [pow_two_pow_succ, t38]; decide
private theorem t40 :
    (3 : ZMod P) ^ (2:ℕ) ^ 40 =
      366246451202105069641168558376416242197964962 := by
  rw [pow_two_pow_succ, t39]; decide
private theorem t41 :
    (3 : ZMod P) ^ (2:ℕ) ^ 41 =
      37516490997534013525469519989684066495755343 := by
  rw [pow_two_pow_succ, t40]; decide
private theorem t42 :
    (3 : ZMod P) ^ (2:ℕ) ^ 42 =
      400448316083173955401854217251586113437609844 := by
  rw [pow_two_pow_succ, t41]; decide
private theorem t43 :
    (3 : ZMod P) ^ (2:ℕ) ^ 43 =
      307954038683137269485076928003457250355092474 := by
  rw [pow_two_pow_succ, t42]; decide
private theorem t44 :
    (3 : ZMod P) ^ (2:ℕ) ^ 44 =
      116870783921704600483259809871663709223695216 := by
  rw [pow_two_pow_succ, t43]; decide
private theorem t45 :
    (3 : ZMod P) ^ (2:ℕ) ^ 45 =
      10917293518269861104354780724029591933551652 := by
  rw [pow_two_pow_succ, t44]; decide
private theorem t46 :
    (3 : ZMod P) ^ (2:ℕ) ^ 46 =
      190461425602578653797009486388618269521709037 := by
  rw [pow_two_pow_succ, t45]; decide
private theorem t47 :
    (3 : ZMod P) ^ (2:ℕ) ^ 47 =
      146807996665929978366138384071115746392577896 := by
  rw [pow_two_pow_succ, t46]; decide
private theorem t48 :
    (3 : ZMod P) ^ (2:ℕ) ^ 48 =
      175182653043435928195905773340791360242951568 := by
  rw [pow_two_pow_succ, t47]; decide
private theorem t49 :
    (3 : ZMod P) ^ (2:ℕ) ^ 49 =
      431085466625717462879378083955444613918340488 := by
  rw [pow_two_pow_succ, t48]; decide
private theorem t50 :
    (3 : ZMod P) ^ (2:ℕ) ^ 50 =
      161085004812691073933578052657465649769867421 := by
  rw [pow_two_pow_succ, t49]; decide
private theorem t51 :
    (3 : ZMod P) ^ (2:ℕ) ^ 51 =
      388838391124900859858102510252968653277035725 := by
  rw [pow_two_pow_succ, t50]; decide
private theorem t52 :
    (3 : ZMod P) ^ (2:ℕ) ^ 52 =
      494070591697919200950523666145316806823709010 := by
  rw [pow_two_pow_succ, t51]; decide
private theorem t53 :
    (3 : ZMod P) ^ (2:ℕ) ^ 53 =
      218081012537963646310164512701106995858611845 := by
  rw [pow_two_pow_succ, t52]; decide
private theorem t54 :
    (3 : ZMod P) ^ (2:ℕ) ^ 54 =
      198693054029711715356858780010249925766184519 := by
  rw [pow_two_pow_succ, t53]; decide
private theorem t55 :
    (3 : ZMod P) ^ (2:ℕ) ^ 55 =
      85363313878294650466880555528126924600064442 := by
  rw [pow_two_pow_succ, t54]; decide
private theorem t56 :
    (3 : ZMod P) ^ (2:ℕ) ^ 56 =
      309762540149493372879266525549650174076111191 := by
  rw [pow_two_pow_succ, t55]; decide
private theorem t57 :
    (3 : ZMod P) ^ (2:ℕ) ^ 57 =
      458185315034142609794885624024342276238221453 := by
  rw [pow_two_pow_succ, t56]; decide
private theorem t58 :
    (3 : ZMod P) ^ (2:ℕ) ^ 58 =
      5884516228175349974375661441815807232739751 := by
  rw [pow_two_pow_succ, t57]; decide
private theorem t59 :
    (3 : ZMod P) ^ (2:ℕ) ^ 59 =
      125243603898337962577388483345161714449241262 := by
  rw [pow_two_pow_succ, t58]; decide
private theorem t60 :
    (3 : ZMod P) ^ (2:ℕ) ^ 60 =
      443315487208603083520741135863538850131432888 := by
  rw [pow_two_pow_succ, t59]; decide
private theorem t61 :
    (3 : ZMod P) ^ (2:ℕ) ^ 61 =
      250719677586182580387202822637695019274273855 := by
  rw [pow_two_pow_succ, t60]; decide
private theorem t62 :
    (3 : ZMod P) ^ (2:ℕ) ^ 62 =
      387380556295086424947356766906573581582515146 := by
  rw [pow_two_pow_succ, t61]; decide
private theorem t63 :
    (3 : ZMod P) ^ (2:ℕ) ^ 63 =
      211246635529944264671496494925444936856219865 := by
  rw [pow_two_pow_succ, t62]; decide
private theorem t64 :
    (3 : ZMod P) ^ (2:ℕ) ^ 64 =
      284810214986218143793267421417704775487839591 := by
  rw [pow_two_pow_succ, t63]; decide
private theorem t65 :
    (3 : ZMod P) ^ (2:ℕ) ^ 65 =
      321632029719295338664956554392691409482085440 := by
  rw [pow_two_pow_succ, t64]; decide
private theorem t66 :
    (3 : ZMod P) ^ (2:ℕ) ^ 66 =
      319576065596134066006506453601278286554293322 := by
  rw [pow_two_pow_succ, t65]; decide
private theorem t67 :
    (3 : ZMod P) ^ (2:ℕ) ^ 67 =
      142466501196165763679317393657119139845034556 := by
  rw [pow_two_pow_succ, t66]; decide
private theorem t68 :
    (3 : ZMod P) ^ (2:ℕ) ^ 68 =
      10619059752848108023544096887062110841654772 := by
  rw [pow_two_pow_succ, t67]; decide
private theorem t69 :
    (3 : ZMod P) ^ (2:ℕ) ^ 69 =
      401883220074881167759681183240419239960112431 := by
  rw [pow_two_pow_succ, t68]; decide
private theorem t70 :
    (3 : ZMod P) ^ (2:ℕ) ^ 70 =
      334228501743489888561059473673704637587428807 := by
  rw [pow_two_pow_succ, t69]; decide
private theorem t71 :
    (3 : ZMod P) ^ (2:ℕ) ^ 71 =
      476977930118827207530876397913137871167343522 := by
  rw [pow_two_pow_succ, t70]; decide
private theorem t72 :
    (3 : ZMod P) ^ (2:ℕ) ^ 72 =
      234640095172182313141487939041506985341056116 := by
  rw [pow_two_pow_succ, t71]; decide
private theorem t73 :
    (3 : ZMod P) ^ (2:ℕ) ^ 73 =
      496998126544769284401971638117549067644128424 := by
  rw [pow_two_pow_succ, t72]; decide
private theorem t74 :
    (3 : ZMod P) ^ (2:ℕ) ^ 74 =
      492522273136699946112858601323019730913794411 := by
  rw [pow_two_pow_succ, t73]; decide
private theorem t75 :
    (3 : ZMod P) ^ (2:ℕ) ^ 75 =
      459743871204533180201529082696054014248577366 := by
  rw [pow_two_pow_succ, t74]; decide
private theorem t76 :
    (3 : ZMod P) ^ (2:ℕ) ^ 76 =
      187705060168427566008673319702813640502283016 := by
  rw [pow_two_pow_succ, t75]; decide
private theorem t77 :
    (3 : ZMod P) ^ (2:ℕ) ^ 77 =
      257803371790487146467318760414283284574295568 := by
  rw [pow_two_pow_succ, t76]; decide
private theorem t78 :
    (3 : ZMod P) ^ (2:ℕ) ^ 78 =
      352919358525247388819700196321327646702707664 := by
  rw [pow_two_pow_succ, t77]; decide
private theorem t79 :
    (3 : ZMod P) ^ (2:ℕ) ^ 79 =
      512079032610142263863606445450573757581045274 := by
  rw [pow_two_pow_succ, t78]; decide
private theorem t80 :
    (3 : ZMod P) ^ (2:ℕ) ^ 80 =
      193204449397251045170568398538535111470971274 := by
  rw [pow_two_pow_succ, t79]; decide
private theorem t81 :
    (3 : ZMod P) ^ (2:ℕ) ^ 81 =
      368671711733163790865834342397148237798858578 := by
  rw [pow_two_pow_succ, t80]; decide
private theorem t82 :
    (3 : ZMod P) ^ (2:ℕ) ^ 82 =
      47477591030681863381806306468383460783553331 := by
  rw [pow_two_pow_succ, t81]; decide
private theorem t83 :
    (3 : ZMod P) ^ (2:ℕ) ^ 83 =
      111574009395845430734179425156581777918149577 := by
  rw [pow_two_pow_succ, t82]; decide
private theorem t84 :
    (3 : ZMod P) ^ (2:ℕ) ^ 84 =
      256016991212339944603469015845503507707151250 := by
  rw [pow_two_pow_succ, t83]; decide
private theorem t85 :
    (3 : ZMod P) ^ (2:ℕ) ^ 85 =
      186979977003210296044383504125491166393457935 := by
  rw [pow_two_pow_succ, t84]; decide
private theorem t86 :
    (3 : ZMod P) ^ (2:ℕ) ^ 86 =
      466462990371743741125566547032130458181980445 := by
  rw [pow_two_pow_succ, t85]; decide
private theorem t87 :
    (3 : ZMod P) ^ (2:ℕ) ^ 87 =
      171534527410354455090531258748572478225800345 := by
  rw [pow_two_pow_succ, t86]; decide
private theorem t88 :
    (3 : ZMod P) ^ (2:ℕ) ^ 88 =
      173100486148123863463848980706657250644102034 := by
  rw [pow_two_pow_succ, t87]; decide
private theorem t89 :
    (3 : ZMod P) ^ (2:ℕ) ^ 89 =
      55305438187426336749392123046787995653869099 := by
  rw [pow_two_pow_succ, t88]; decide
private theorem t90 :
    (3 : ZMod P) ^ (2:ℕ) ^ 90 =
      204428427399520612574570288443189385412618443 := by
  rw [pow_two_pow_succ, t89]; decide
private theorem t91 :
    (3 : ZMod P) ^ (2:ℕ) ^ 91 =
      323443107831339335617935444646518752558673304 := by
  rw [pow_two_pow_succ, t90]; decide
private theorem t92 :
    (3 : ZMod P) ^ (2:ℕ) ^ 92 =
      165013126250566004394818934918086091202224757 := by
  rw [pow_two_pow_succ, t91]; decide
private theorem t93 :
    (3 : ZMod P) ^ (2:ℕ) ^ 93 =
      113035998679924246326873624599134915069551213 := by
  rw [pow_two_pow_succ, t92]; decide
private theorem t94 :
    (3 : ZMod P) ^ (2:ℕ) ^ 94 =
      103680241297095573852152605797921642849326873 := by
  rw [pow_two_pow_succ, t93]; decide
private theorem t95 :
    (3 : ZMod P) ^ (2:ℕ) ^ 95 =
      181729020626515142484670412824035857970710531 := by
  rw [pow_two_pow_succ, t94]; decide
private theorem t96 :
    (3 : ZMod P) ^ (2:ℕ) ^ 96 =
      166396441772951483670115577152423113254814143 := by
  rw [pow_two_pow_succ, t95]; decide
private theorem t97 :
    (3 : ZMod P) ^ (2:ℕ) ^ 97 =
      255195864952365437047572693581039225948298889 := by
  rw [pow_two_pow_succ, t96]; decide
private theorem t98 :
    (3 : ZMod P) ^ (2:ℕ) ^ 98 =
      350384320353341254486382441317000819473355582 := by
  rw [pow_two_pow_succ, t97]; decide
private theorem t99 :
    (3 : ZMod P) ^ (2:ℕ) ^ 99 =
      323962129032769791290008216464921923002014507 := by
  rw [pow_two_pow_succ, t98]; decide
private theorem t100 :
    (3 : ZMod P) ^ (2:ℕ) ^ 100 =
      488681542361046836171369995978745810284477890 := by
  rw [pow_two_pow_succ, t99]; decide
private theorem t101 :
    (3 : ZMod P) ^ (2:ℕ) ^ 101 =
      300138347250519757159341431785407442858610428 := by
  rw [pow_two_pow_succ, t100]; decide
private theorem t102 :
    (3 : ZMod P) ^ (2:ℕ) ^ 102 =
      204125064257637546042571215596111653901214226 := by
  rw [pow_two_pow_succ, t101]; decide
private theorem t103 :
    (3 : ZMod P) ^ (2:ℕ) ^ 103 =
      82521164727141684192467816669923470106815109 := by
  rw [pow_two_pow_succ, t102]; decide
private theorem t104 :
    (3 : ZMod P) ^ (2:ℕ) ^ 104 =
      298480834532824045997320952039526653971267962 := by
  rw [pow_two_pow_succ, t103]; decide
private theorem t105 :
    (3 : ZMod P) ^ (2:ℕ) ^ 105 =
      153848366362746713627606852847105690684036573 := by
  rw [pow_two_pow_succ, t104]; decide
private theorem t106 :
    (3 : ZMod P) ^ (2:ℕ) ^ 106 =
      98853499908411620143428207943573723726682880 := by
  rw [pow_two_pow_succ, t105]; decide
private theorem t107 :
    (3 : ZMod P) ^ (2:ℕ) ^ 107 =
      49166371448583346334072199695076761982081409 := by
  rw [pow_two_pow_succ, t106]; decide
private theorem t108 :
    (3 : ZMod P) ^ (2:ℕ) ^ 108 =
      107231320174808231040801860416353346591817242 := by
  rw [pow_two_pow_succ, t107]; decide
private theorem t109 :
    (3 : ZMod P) ^ (2:ℕ) ^ 109 =
      476069077944954850285107364108720575164799654 := by
  rw [pow_two_pow_succ, t108]; decide
private theorem t110 :
    (3 : ZMod P) ^ (2:ℕ) ^ 110 =
      172455520018430883497531201250364307770279681 := by
  rw [pow_two_pow_succ, t109]; decide
private theorem t111 :
    (3 : ZMod P) ^ (2:ℕ) ^ 111 =
      91719442714531073687102867200897697183985357 := by
  rw [pow_two_pow_succ, t110]; decide
private theorem t112 :
    (3 : ZMod P) ^ (2:ℕ) ^ 112 =
      161035539375559747156100569900470084452443485 := by
  rw [pow_two_pow_succ, t111]; decide
private theorem t113 :
    (3 : ZMod P) ^ (2:ℕ) ^ 113 =
      299501751630545735392172153411093733730103435 := by
  rw [pow_two_pow_succ, t112]; decide
private theorem t114 :
    (3 : ZMod P) ^ (2:ℕ) ^ 114 =
      366345990610764772004027925249263315942042469 := by
  rw [pow_two_pow_succ, t113]; decide
private theorem t115 :
    (3 : ZMod P) ^ (2:ℕ) ^ 115 =
      25814399904289867239001237445627198882536907 := by
  rw [pow_two_pow_succ, t114]; decide
private theorem t116 :
    (3 : ZMod P) ^ (2:ℕ) ^ 116 =
      416494561833275944183578220541208201728413702 := by
  rw [pow_two_pow_succ, t115]; decide
private theorem t117 :
    (3 : ZMod P) ^ (2:ℕ) ^ 117 =
      457594076730487057773238868185998295110495146 := by
  rw [pow_two_pow_succ, t116]; decide
private theorem t118 :
    (3 : ZMod P) ^ (2:ℕ) ^ 118 =
      451283414796834480949092971387014768591572899 := by
  rw [pow_two_pow_succ, t117]; decide
private theorem t119 :
    (3 : ZMod P) ^ (2:ℕ) ^ 119 =
      140059715303081394369003773764147809497922405 := by
  rw [pow_two_pow_succ, t118]; decide
private theorem t120 :
    (3 : ZMod P) ^ (2:ℕ) ^ 120 =
      213075158330039751471403643818766656005859621 := by
  rw [pow_two_pow_succ, t119]; decide
private theorem t121 :
    (3 : ZMod P) ^ (2:ℕ) ^ 121 =
      147035750475467461306079408287879950675461613 := by
  rw [pow_two_pow_succ, t120]; decide
private theorem t122 :
    (3 : ZMod P) ^ (2:ℕ) ^ 122 =
      303122960184063223436176822782664090116234752 := by
  rw [pow_two_pow_succ, t121]; decide
private theorem t123 :
    (3 : ZMod P) ^ (2:ℕ) ^ 123 =
      222911154094981604118591579347896681669122778 := by
  rw [pow_two_pow_succ, t122]; decide
private theorem t124 :
    (3 : ZMod P) ^ (2:ℕ) ^ 124 =
      201859378557091374622862194679144845036305987 := by
  rw [pow_two_pow_succ, t123]; decide
private theorem t125 :
    (3 : ZMod P) ^ (2:ℕ) ^ 125 =
      283345807019858667710492938642451157754689990 := by
  rw [pow_two_pow_succ, t124]; decide
private theorem t126 :
    (3 : ZMod P) ^ (2:ℕ) ^ 126 =
      30742729955359338744598720664508032047447458 := by
  rw [pow_two_pow_succ, t125]; decide
private theorem t127 :
    (3 : ZMod P) ^ (2:ℕ) ^ 127 =
      275540573860538866948356627790224597674869502 := by
  rw [pow_two_pow_succ, t126]; decide
private theorem t128 :
    (3 : ZMod P) ^ (2:ℕ) ^ 128 =
      208568125359066634716790655528659071138438340 := by
  rw [pow_two_pow_succ, t127]; decide

private theorem hx :
    (3 : ZMod P) ^ (1526377:ℕ) =
      165442391133511873843757061499086348529007507 := by
  rw [show (1526377:ℕ)
      = 2^20 + 2^18 + 2^17 + 2^16 + 2^14 + 2^11 + 2^9 + 2^6 + 2^5 + 2^3 + 2^0
      from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    pow_add, pow_add, t20, t18, t17, t16, t14, t11, t9, t6, t5, t3, t0]
  decide

private theorem u0 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 0 =
      165442391133511873843757061499086348529007507 := by
  norm_num
private theorem u1 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 1 =
      252491231045842532460281366117144947226579539 := by
  rw [pow_two_pow_succ, u0]; decide
private theorem u2 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 2 =
      74902514807773944999055024687856237074168446 := by
  rw [pow_two_pow_succ, u1]; decide
private theorem u3 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 3 =
      20756878684854500717566572802696680212012294 := by
  rw [pow_two_pow_succ, u2]; decide
private theorem u4 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 4 =
      59491175669817562044619697740437279118374681 := by
  rw [pow_two_pow_succ, u3]; decide
private theorem u5 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 5 =
      19705133000043493852178028492792885490704817 := by
  rw [pow_two_pow_succ, u4]; decide
private theorem u6 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 6 =
      441484568520604980021204677872024470169377201 := by
  rw [pow_two_pow_succ, u5]; decide
private theorem u7 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 7 =
      503911945422408542430726910976590914921471293 := by
  rw [pow_two_pow_succ, u6]; decide
private theorem u8 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 8 =
      350888053420913715459704107627506545142436834 := by
  rw [pow_two_pow_succ, u7]; decide
private theorem u9 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 9 =
      154896725565346470074631680802275227772841288 := by
  rw [pow_two_pow_succ, u8]; decide
private theorem u10 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 10 =
      115295748726750951740534046986662583182101205 := by
  rw [pow_two_pow_succ, u9]; decide
private theorem u11 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 11 =
      168114444632895882992089075385743793753582135 := by
  rw [pow_two_pow_succ, u10]; decide
private theorem u12 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 12 =
      61486686179659891361579232885469539511206495 := by
  rw [pow_two_pow_succ, u11]; decide
private theorem u13 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 13 =
      418939504286438331335641861683491589651230855 := by
  rw [pow_two_pow_succ, u12]; decide
private theorem u14 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 14 =
      46490253687168277219671642348839843884215326 := by
  rw [pow_two_pow_succ, u13]; decide
private theorem u15 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 15 =
      107869720462553983435706801544014060884131877 := by
  rw [pow_two_pow_succ, u14]; decide
private theorem u16 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 16 =
      41155303068513162526819483087668546755081070 := by
  rw [pow_two_pow_succ, u15]; decide
private theorem u17 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 17 =
      423532536812620291353166052205070956489655615 := by
  rw [pow_two_pow_succ, u16]; decide
private theorem u18 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 18 =
      248544955080621094657364764256625904740030364 := by
  rw [pow_two_pow_succ, u17]; decide
private theorem u19 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 19 =
      251746115958219918268329526997464074899345762 := by
  rw [pow_two_pow_succ, u18]; decide
private theorem u20 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 20 =
      443939327251835144243046899295703621578101754 := by
  rw [pow_two_pow_succ, u19]; decide
private theorem u21 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 21 =
      228931388278169699104460483514812163150804846 := by
  rw [pow_two_pow_succ, u20]; decide
private theorem u22 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 22 =
      205364124346110469089979147103591181181686448 := by
  rw [pow_two_pow_succ, u21]; decide
private theorem u23 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 23 =
      53048862176533800877789497199218475036487590 := by
  rw [pow_two_pow_succ, u22]; decide
private theorem u24 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 24 =
      504869989990548774748056092280452204122481304 := by
  rw [pow_two_pow_succ, u23]; decide
private theorem u25 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 25 =
      222306116354162303962779191942004094397908601 := by
  rw [pow_two_pow_succ, u24]; decide
private theorem u26 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 26 =
      136406827131585333259867612941902401943313557 := by
  rw [pow_two_pow_succ, u25]; decide
private theorem u27 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 27 =
      457575734594855203577752883817804683261453392 := by
  rw [pow_two_pow_succ, u26]; decide
private theorem u28 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 28 =
      503229015571099967024509318479652410348500259 := by
  rw [pow_two_pow_succ, u27]; decide
private theorem u29 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 29 =
      508102365054867878155960299064998289684974350 := by
  rw [pow_two_pow_succ, u28]; decide
private theorem u30 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 30 =
      146431677477153089530812642393998223145997780 := by
  rw [pow_two_pow_succ, u29]; decide
private theorem u31 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 31 =
      464188730805935023450675828056495786875815813 := by
  rw [pow_two_pow_succ, u30]; decide
private theorem u32 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 32 =
      31252346752840775151348904710386482344417203 := by
  rw [pow_two_pow_succ, u31]; decide
private theorem u33 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 33 =
      269635718106726877400924717704574582565970341 := by
  rw [pow_two_pow_succ, u32]; decide
private theorem u34 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 34 =
      442087258993786765077430809755105503840571111 := by
  rw [pow_two_pow_succ, u33]; decide
private theorem u35 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 35 =
      270218410978901620736975301916982219152027637 := by
  rw [pow_two_pow_succ, u34]; decide
private theorem u36 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 36 =
      107165967252664035648409835548965817385560087 := by
  rw [pow_two_pow_succ, u35]; decide
private theorem u37 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 37 =
      452376790020165934147892059664999821647627726 := by
  rw [pow_two_pow_succ, u36]; decide
private theorem u38 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 38 =
      237612590060408135377964525708356855779062433 := by
  rw [pow_two_pow_succ, u37]; decide
private theorem u39 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 39 =
      518594338422257761490600694587612721013154796 := by
  rw [pow_two_pow_succ, u38]; decide
private theorem u40 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 40 =
      267794072400213461871244836735505495304520021 := by
  rw [pow_two_pow_succ, u39]; decide
private theorem u41 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 41 =
      365337861026457595870404916062457060546109599 := by
  rw [pow_two_pow_succ, u40]; decide
private theorem u42 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 42 =
      46704781661992404565409656241410042201090653 := by
  rw [pow_two_pow_succ, u41]; decide
private theorem u43 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 43 =
      28515015503189924719566915708598887936264738 := by
  rw [pow_two_pow_succ, u42]; decide
private theorem u44 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 44 =
      255721080856402504941978921107790175983846391 := by
  rw [pow_two_pow_succ, u43]; decide
private theorem u45 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 45 =
      502081633683545711896957044957778832151335002 := by
  rw [pow_two_pow_succ, u44]; decide
private theorem u46 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 46 =
      219264206465246628747111970480027036763989561 := by
  rw [pow_two_pow_succ, u45]; decide
private theorem u47 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 47 =
      22655146422102077062203635223550389450055816 := by
  rw [pow_two_pow_succ, u46]; decide
private theorem u48 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 48 =
      197734104212175648341936692527254499772619407 := by
  rw [pow_two_pow_succ, u47]; decide
private theorem u49 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 49 =
      416272025216931530023784927738548659585330285 := by
  rw [pow_two_pow_succ, u48]; decide
private theorem u50 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 50 =
      486764676856582745952229725002501253005284931 := by
  rw [pow_two_pow_succ, u49]; decide
private theorem u51 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 51 =
      72032578742637462577053375150428014416408930 := by
  rw [pow_two_pow_succ, u50]; decide
private theorem u52 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 52 =
      396161186770838951125429500462746854739353749 := by
  rw [pow_two_pow_succ, u51]; decide
private theorem u53 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 53 =
      451018351781624346696575288519816324944509000 := by
  rw [pow_two_pow_succ, u52]; decide
private theorem u54 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 54 =
      403381626391006942620123807561348701650640727 := by
  rw [pow_two_pow_succ, u53]; decide
private theorem u55 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 55 =
      339186375743646893442461753026045858791126892 := by
  rw [pow_two_pow_succ, u54]; decide
private theorem u56 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 56 =
      263321690917289924733395583690589199595577514 := by
  rw [pow_two_pow_succ, u55]; decide
private theorem u57 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 57 =
      9642347834394121739690203206407468145180989 := by
  rw [pow_two_pow_succ, u56]; decide
private theorem u58 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 58 =
      33045465432207716791311254461917505264638258 := by
  rw [pow_two_pow_succ, u57]; decide
private theorem u59 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 59 =
      384384806318179301009911121931969723174701416 := by
  rw [pow_two_pow_succ, u58]; decide
private theorem u60 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 60 =
      360821573152548099623886284203568060418862108 := by
  rw [pow_two_pow_succ, u59]; decide
private theorem u61 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 61 =
      39950842674332549676323367321726518757583924 := by
  rw [pow_two_pow_succ, u60]; decide
private theorem u62 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 62 =
      425670092232129141949824425906305028566662271 := by
  rw [pow_two_pow_succ, u61]; decide
private theorem u63 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 63 =
      130029878922518002702055953016540741826094250 := by
  rw [pow_two_pow_succ, u62]; decide
private theorem u64 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 64 =
      113431195353810055032580479035059808169079024 := by
  rw [pow_two_pow_succ, u63]; decide
private theorem u65 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 65 =
      328275711275653788554920513983384207813398475 := by
  rw [pow_two_pow_succ, u64]; decide
private theorem u66 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 66 =
      397854505358117510102319150374224655333884944 := by
  rw [pow_two_pow_succ, u65]; decide
private theorem u67 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 67 =
      115383152342375508416841369922219272696950408 := by
  rw [pow_two_pow_succ, u66]; decide
private theorem u68 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 68 =
      97040585452488916077643988078270401654175088 := by
  rw [pow_two_pow_succ, u67]; decide
private theorem u69 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 69 =
      448290698331673994344406502341695360094850160 := by
  rw [pow_two_pow_succ, u68]; decide
private theorem u70 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 70 =
      198841090919985210320502219461116650046438123 := by
  rw [pow_two_pow_succ, u69]; decide
private theorem u71 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 71 =
      183027501564800718714907604153612536421272854 := by
  rw [pow_two_pow_succ, u70]; decide
private theorem u72 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 72 =
      216283551345988436603615113673431482695864209 := by
  rw [pow_two_pow_succ, u71]; decide
private theorem u73 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 73 =
      177180807549604958968976828930378453628316067 := by
  rw [pow_two_pow_succ, u72]; decide
private theorem u74 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 74 =
      46655242111323339314622368543419583372136739 := by
  rw [pow_two_pow_succ, u73]; decide
private theorem u75 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 75 =
      374029501674433080117069602132784195172754142 := by
  rw [pow_two_pow_succ, u74]; decide
private theorem u76 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 76 =
      303882328816222052528517589623915327942551337 := by
  rw [pow_two_pow_succ, u75]; decide
private theorem u77 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 77 =
      49209998975803084085246503665381905822856821 := by
  rw [pow_two_pow_succ, u76]; decide
private theorem u78 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 78 =
      430483708988454284715690219532495151198294327 := by
  rw [pow_two_pow_succ, u77]; decide
private theorem u79 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 79 =
      257427590845934941383461016706320242975975484 := by
  rw [pow_two_pow_succ, u78]; decide
private theorem u80 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 80 =
      361347254941425332664147174637191197287534689 := by
  rw [pow_two_pow_succ, u79]; decide
private theorem u81 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 81 =
      174046965567252837207034395044987297639018478 := by
  rw [pow_two_pow_succ, u80]; decide
private theorem u82 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 82 =
      171072416272973821675462180420207054557577732 := by
  rw [pow_two_pow_succ, u81]; decide
private theorem u83 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 83 =
      405068218423050978629866214202333596698576456 := by
  rw [pow_two_pow_succ, u82]; decide
private theorem u84 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 84 =
      363240040207283669867667430257774011782857352 := by
  rw [pow_two_pow_succ, u83]; decide
private theorem u85 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 85 =
      318957797954517992648853424873693904203718969 := by
  rw [pow_two_pow_succ, u84]; decide
private theorem u86 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 86 =
      299945257371667153934802545025718543159540196 := by
  rw [pow_two_pow_succ, u85]; decide
private theorem u87 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 87 =
      309563278205056499458571050590676398076847948 := by
  rw [pow_two_pow_succ, u86]; decide
private theorem u88 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 88 =
      177115772568825051638617178746224838234159254 := by
  rw [pow_two_pow_succ, u87]; decide
private theorem u89 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 89 =
      151663020871614913862510590843361360330747900 := by
  rw [pow_two_pow_succ, u88]; decide
private theorem u90 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 90 =
      425514312487428790588563460531100599868905615 := by
  rw [pow_two_pow_succ, u89]; decide
private theorem u91 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 91 =
      382975162357337701731816834540170779190687508 := by
  rw [pow_two_pow_succ, u90]; decide
private theorem u92 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 92 =
      210764901871475594480120147966494460052957623 := by
  rw [pow_two_pow_succ, u91]; decide
private theorem u93 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 93 =
      434763951955430367089702270436389313153201865 := by
  rw [pow_two_pow_succ, u92]; decide
private theorem u94 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 94 =
      247505352091962036383807451526385116431432481 := by
  rw [pow_two_pow_succ, u93]; decide
private theorem u95 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 95 =
      314166167584392761377708559195396898189550533 := by
  rw [pow_two_pow_succ, u94]; decide
private theorem u96 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 96 =
      209304479713878626974105457242219197240903891 := by
  rw [pow_two_pow_succ, u95]; decide
private theorem u97 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 97 =
      509321544402420323514549188996637668717114188 := by
  rw [pow_two_pow_succ, u96]; decide
private theorem u98 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 98 =
      231187688103593171176432170493530440267472408 := by
  rw [pow_two_pow_succ, u97]; decide
private theorem u99 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 99 =
      382931535590417462633533727803176618368398490 := by
  rw [pow_two_pow_succ, u98]; decide
private theorem u100 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 100 =
      510194387771344088536506055716406112130263339 := by
  rw [pow_two_pow_succ, u99]; decide
private theorem u101 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 101 =
      93740822327254571030066890487341911457488866 := by
  rw [pow_two_pow_succ, u100]; decide
private theorem u102 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 102 =
      459042228200819013930762858990874783752353161 := by
  rw [pow_two_pow_succ, u101]; decide
private theorem u103 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 103 =
      219020447514987670315412488715142082026774290 := by
  rw [pow_two_pow_succ, u102]; decide
private theorem u104 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 104 =
      51252300963434114284910536713027800924026160 := by
  rw [pow_two_pow_succ, u103]; decide
private theorem u105 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 105 =
      7417314220421406165928028995096207813107169 := by
  rw [pow_two_pow_succ, u104]; decide
private theorem u106 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 106 =
      241835028798627547351619105517517104254118432 := by
  rw [pow_two_pow_succ, u105]; decide
private theorem u107 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 107 =
      148361135708846677927046999078703105247611902 := by
  rw [pow_two_pow_succ, u106]; decide
private theorem u108 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 108 =
      426143754791480064624092445362328696646059801 := by
  rw [pow_two_pow_succ, u107]; decide
private theorem u109 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 109 =
      460603574297143599926392007817442509884045899 := by
  rw [pow_two_pow_succ, u108]; decide
private theorem u110 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 110 =
      51486509090622594703246543434956141612494383 := by
  rw [pow_two_pow_succ, u109]; decide
private theorem u111 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 111 =
      488846629533447444476073840434860452134367106 := by
  rw [pow_two_pow_succ, u110]; decide
private theorem u112 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 112 =
      226346986772659576027459827390474307363830466 := by
  rw [pow_two_pow_succ, u111]; decide
private theorem u113 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 113 =
      7185628547800880143996135288062673633654314 := by
  rw [pow_two_pow_succ, u112]; decide
private theorem u114 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 114 =
      452711579240454384503968936218628066339541538 := by
  rw [pow_two_pow_succ, u113]; decide
private theorem u115 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 115 =
      292286326714059807530605398915817200101818520 := by
  rw [pow_two_pow_succ, u114]; decide
private theorem u116 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 116 =
      184440288348134593141252446328251484241161072 := by
  rw [pow_two_pow_succ, u115]; decide
private theorem u117 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 117 =
      293365863657889630266000728811480672642732752 := by
  rw [pow_two_pow_succ, u116]; decide
private theorem u118 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 118 =
      434507333182180323377643476259977076423905968 := by
  rw [pow_two_pow_succ, u117]; decide
private theorem u119 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 119 =
      254767641214941562458797882558775474410259796 := by
  rw [pow_two_pow_succ, u118]; decide
private theorem u120 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 120 =
      378617742819642335981776145873260038231339392 := by
  rw [pow_two_pow_succ, u119]; decide
private theorem u121 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 121 =
      310203434314666696188233614211469848907459003 := by
  rw [pow_two_pow_succ, u120]; decide
private theorem u122 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 122 =
      343681710474810194684472438365758239853939287 := by
  rw [pow_two_pow_succ, u121]; decide
private theorem u123 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 123 =
      319716748530591765875197368137938642679541616 := by
  rw [pow_two_pow_succ, u122]; decide
private theorem u124 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 124 =
      279145592180509237238598208749740133104522236 := by
  rw [pow_two_pow_succ, u123]; decide
private theorem u125 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 125 =
      73938427385806104769255114516552723990323977 := by
  rw [pow_two_pow_succ, u124]; decide
private theorem u126 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 126 =
      282973769376772806612563346396618117698308472 := by
  rw [pow_two_pow_succ, u125]; decide
private theorem u127 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 127 =
      519399178373681289045835343167880067297574912 := by
  rw [pow_two_pow_succ, u126]; decide
private theorem u128 :
    (165442391133511873843757061499086348529007507 : ZMod P) ^ (2:ℕ) ^ 128 =
      1 := by
  rw [pow_two_pow_succ, u127]; decide

private theorem cert_main : (3 : ZMod P) ^ (P - 1) = 1 := by
  rw [show P - 1 = 1526377 * 2 ^ 128 from by norm_num, pow_mul, hx, u128]

private theorem cert_q2 : (3 : ZMod P) ^ ((P - 1) / 2) ≠ 1 := by
  rw [show (P - 1) / 2 = 1526377 * 2 ^ 127 from by norm_num, pow_mul, hx, u127]
  decide

private theorem cert_qh : (3 : ZMod P) ^ ((P - 1) / 1526377) ≠ 1 := by
  rw [show (P - 1) / 1526377 = 2 ^ 128 from by norm_num, t128]
  decide

theorem prime_P : Nat.Prime P := by
  refine lucas_primality P 3 cert_main ?_
  intro q hq hdvd
  rw [show P - 1 = 1526377 * 2 ^ 128 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · have hqh : q = 1526377 :=
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
    subst hqh
    exact cert_qh
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst hq2
    exact cert_q2

local instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩

private theorem g_def :
    (3 : ZMod P) ^ ((P - 1) / 64) =
      343681710474810194684472438365758239853939287 := by
  rw [show (P - 1) / 64 = 1526377 * 2 ^ 122 from by norm_num, pow_mul, hx, u122]

/-- The order-64 certificate. -/
theorem orderOf_gP :
    orderOf (343681710474810194684472438365758239853939287 : ZMod P) = 64 := by
  have h5 : ¬ (343681710474810194684472438365758239853939287 : ZMod P) ^ (2:ℕ) ^ 5 = 1 := by
    decide
  have h6 : (343681710474810194684472438365758239853939287 : ZMod P) ^ (2:ℕ) ^ 6 = 1 := by
    decide
  have h := orderOf_eq_prime_pow
    (x := (343681710474810194684472438365758239853939287 : ZMod P)) h5 h6
  norm_num at h
  exact h

/-! ## The conditional pin -/

private theorem choose_64_5 : (64 : ℕ).choose 5 = 7624512 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_32_5 : (32 : ℕ).choose 5 = 201376 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- **The μ = 6 conditional literal-budget pin**: given only the in-tree divisibility
hypothesis, `δ* = 59/64` exactly at `ε* = 2⁻¹²⁸` for the dimension-4 (rate `1/16`) code
on the 64-point smooth domain — beyond Johnson (`3/4`), below capacity (`15/16`). -/
theorem deltaStar_pin_mu6_dim4_of_not_dvd
    (hndvd : ∀ d₁ ∈ sigData (2 ^ 5) 5, ∀ d₂ ∈ sigData (2 ^ 5) 5,
      d₁ ≠ d₂ → ¬ (P : ℤ) ∣ collisionResultant 6 d₁ d₂) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode
          (343681710474810194684472438365758239853939287 : ZMod P) 64 3)
        (1 / 2 ^ 128)
      = 59 / 64 := by
  haveI : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_march_deltaStar_pin_of_not_dvd (p := P) (μ := 6) (r := 5)
    (g := (343681710474810194684472438365758239853939287 : ZMod P)) (n := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact orderOf_gP) (by norm_num) hndvd
    (1 / 2 ^ 128) ?hlo ?hhi
  case hlo =>
    have hc : ((64 : ℕ).choose 5 / 5 : ℕ) = 1524902 := by rw [choose_64_5]
    rw [hc]
    exact band_lo_general (by norm_num) (by norm_num)
  case hhi =>
    have hc : (2 ^ 5 * (2 ^ (6 - 1)).choose 5 : ℕ) = 6444032 := by
      show (2 ^ 5 * (32 : ℕ).choose 5 : ℕ) = 6444032
      rw [choose_32_5]
      norm_num
    rw [hc]
    exact band_hi_general (e := 6444031) (q := P) (by norm_num)
  rw [h]
  have e2 : (((5 : ℕ)) : ℝ≥0) = (5 : ℝ≥0) := by norm_num
  rw [e2]
  have hd : (5 : ℝ≥0) / ((2 : ℝ≥0) ^ 6) = 5 / 64 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- **Mahler/Landau handoff for the μ = 6 literal pin.**  If every relevant collision
resultant has absolute value below the certified prime `P`, the named divisibility
hypothesis of `deltaStar_pin_mu6_dim4_of_not_dvd` is discharged. -/
theorem deltaStar_pin_mu6_dim4_of_collisionResultant_natAbs_lt
    (hbound : ∀ d₁ ∈ sigData (2 ^ 5) 5, ∀ d₂ ∈ sigData (2 ^ 5) 5,
      d₁ ≠ d₂ → (collisionResultant 6 d₁ d₂).natAbs < P) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode
          (343681710474810194684472438365758239853939287 : ZMod P) 64 3)
        (1 / 2 ^ 128)
      = 59 / 64 := by
  exact deltaStar_pin_mu6_dim4_of_not_dvd
    (collisionResultant_not_dvd_of_forall_natAbs_lt (p := P) (m := 6) (r := 5)
      (by omega) hbound)

/-- The μ = 6 squared Landau envelope is exactly `2^255`. -/
theorem landauSqEnvelope_mu6_eq_two_pow_255 :
    landauSqEnvelope (2 ^ 5) = 2 ^ 255 := by
  norm_num [landauSqEnvelope]

/-- The certified prime `P` is large enough for the μ = 6 squared Landau envelope:
`(4·32)^32·2^31 = 2^255 < P^2`. -/
theorem landauSqEnvelope_mu6_lt_P_sq : landauSqEnvelope (2 ^ 5) < P ^ 2 := by
  have hstrict : landauSqEnvelope (2 ^ 5) < (2 ^ 128 : ℕ) ^ 2 := by
    rw [landauSqEnvelope_mu6_eq_two_pow_255]
    norm_num
  have hp : 2 ^ 128 ≤ P := by norm_num [P]
  exact lt_of_lt_of_le hstrict (Nat.pow_le_pow_left hp 2)

/-- **Squared Mahler/Landau handoff for the μ = 6 literal pin.**  It is enough to bound
every relevant collision resultant by the μ = 6 squared Landau envelope; the envelope is
already below `P²`, so the finite divisibility hypothesis follows. -/
theorem deltaStar_pin_mu6_dim4_of_collisionResultant_natAbs_sq_bound
    (hbound : ∀ d₁ ∈ sigData (2 ^ 5) 5, ∀ d₂ ∈ sigData (2 ^ 5) 5,
      d₁ ≠ d₂ → (collisionResultant 6 d₁ d₂).natAbs ^ 2 ≤ landauSqEnvelope (2 ^ 5)) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode
          (343681710474810194684472438365758239853939287 : ZMod P) 64 3)
        (1 / 2 ^ 128)
      = 59 / 64 := by
  exact deltaStar_pin_mu6_dim4_of_not_dvd
    (collisionResultant_not_dvd_of_uniform_natAbs_sq_bound (p := P)
      (B := landauSqEnvelope (2 ^ 5)) (m := 6) (r := 5) (by norm_num)
      hbound landauSqEnvelope_mu6_lt_P_sq)

/-- **Cyclotomic Landau handoff for the μ = 6 literal pin.**  A proof of the single
analytic obligation `cyclotomicLandauSqBound 6` closes the certified dimension-4 pin
`δ* = 59/64` at `ε* = 2^-128`. -/
theorem deltaStar_pin_mu6_dim4_of_cyclotomicLandauSqBound
    (hL : cyclotomicLandauSqBound 6) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode
          (343681710474810194684472438365758239853939287 : ZMod P) 64 3)
        (1 / 2 ^ 128)
      = 59 / 64 := by
  exact deltaStar_pin_mu6_dim4_of_not_dvd
    (collisionResultant_not_dvd_of_cyclotomicLandauSqBound (p := P)
      (m := 6) (r := 5) hL (by norm_num) (by norm_num)
      landauSqEnvelope_mu6_lt_P_sq)

/-- **Promoted μ = 6 dimension-4 literal pin.**  The Parseval + AM-GM proof of
`cyclotomicLandauSqBound 6` discharges the collision-resultant divisibility route, so the
certified code has `δ* = 59/64` at `ε* = 2^-128` without any remaining named bad-side
hypothesis. -/
theorem deltaStar_pin_mu6_dim4 :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode
          (343681710474810194684472438365758239853939287 : ZMod P) 64 3)
        (1 / 2 ^ 128)
      = 59 / 64 := by
  exact deltaStar_pin_mu6_dim4_of_cyclotomicLandauSqBound
    (cyclotomicLandauSqBound_proved (m := 6) (by norm_num))

/-- The Mahler/Landau target `2^143` is strictly below the certified prime `P`. -/
theorem two_pow_143_lt_P : (2 : ℕ) ^ 143 < P := by
  have hpow : (2 : ℕ) ^ 143 = 2 ^ 15 * 2 ^ 128 := by
    rw [show 143 = 15 + 128 by norm_num, pow_add]
  have hcoeff : (2 : ℕ) ^ 15 < 1526377 := by norm_num
  have hscaled : (2 : ℕ) ^ 15 * 2 ^ 128 < 1526377 * 2 ^ 128 :=
    Nat.mul_lt_mul_of_pos_right hcoeff (by positivity)
  have hPm1 : P - 1 = 1526377 * 2 ^ 128 := by norm_num
  rw [hpow]
  omega

end ArkLib.ProximityGap.Mu6ConditionalPin

/-! ## Axiom audit — kernel-clean. -/
#print axioms
  ArkLib.ProximityGap.Mu6ConditionalPin.kkh26_deltaStar_pin_of_interior_ceiling_of_not_dvd
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.kkh26_march_deltaStar_pin_of_not_dvd
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.prime_P
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.orderOf_gP
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.deltaStar_pin_mu6_dim4_of_not_dvd
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.landauSqEnvelope_mu6_eq_two_pow_255
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.landauSqEnvelope_mu6_lt_P_sq
#print axioms
  ArkLib.ProximityGap.Mu6ConditionalPin.deltaStar_pin_mu6_dim4_of_collisionResultant_natAbs_sq_bound
#print axioms
  ArkLib.ProximityGap.Mu6ConditionalPin.deltaStar_pin_mu6_dim4_of_cyclotomicLandauSqBound
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.deltaStar_pin_mu6_dim4
#print axioms ArkLib.ProximityGap.Mu6ConditionalPin.two_pow_143_lt_P
#print axioms
  ArkLib.ProximityGap.Mu6ConditionalPin.deltaStar_pin_mu6_dim4_of_collisionResultant_natAbs_lt
