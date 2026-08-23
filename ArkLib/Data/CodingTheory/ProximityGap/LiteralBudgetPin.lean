/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch
import ArkLib.Data.CodingTheory.ProximityGap.StaircaseBandTheorem
import Mathlib.NumberTheory.LucasPrimality

/-!
# The first in-window `δ*` pin at the literal challenge budget `ε* = 2⁻¹²⁸` (#371)

Every landed in-window pin so far evaluates at a toy `ε*` (`18/12289`, `910/(2³²+81)`, …);
the literal-budget results (`StaircaseBandTheorem`) live below the ladder reach.  This file
pins `δ*` **at the literal challenge error** `ε* = 2⁻¹²⁸`, strictly inside the open window:

  `mcaDeltaStar(evalCode g 32 6, 2⁻¹²⁸) = 3/4` — **exactly** —

for the dimension-7 (rate `7/32`) code on the 32-point smooth domain `⟨g⟩ ⊆ F_P^×`,
`P = 1314883·2¹²⁸ + 1 ≈ 2^148.33`.  Beyond Johnson (`1 − √(7/32) ≈ 0.532 < 3/4`), below
capacity (`25/32`).  The `ε*`-band mechanism: at `ε* = 2⁻¹²⁸` the budget band is the
field-size band `q ∈ [1314787·2¹²⁸, 3294720·2¹²⁸)` (`1314787 = ⌊C(32,8)/8⌋` the glueing
floor, `3294720 = 2⁸·C(16,8)` the KKH26 ceiling spectrum), and `P` is a Proth prime chosen
inside it — `P − 1 = 1314883·2¹²⁸` keeps the Lucas certificate at two cofactor checks
(witness `3`) and makes `2¹²⁸ ∣ P − 1`, so the order-32 element is a chain value.

Method as in `CertifiedRungPrime.lean`: literal squaring chains (`t_k = 3^(2^k)`,
`u_k = (3^1314883)^(2^k)`, ~260 generated one-mulmod `decide` steps), `lucas_primality`,
`orderOf_eq_prime_pow`, then `kkh26_march_deltaStar_pin` with the `StaircaseBandTheorem`
budget bridges `band_lo_general`/`band_hi_general`.

Probe: `scripts/probes/probe_literal_budget_pin.py` (deterministic Miller–Rabin, exact
chain replay, band arithmetic at the literal budget).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ProximityGap.StaircaseBandTheorem

namespace ArkLib.ProximityGap.LiteralBudgetPin

/-- The certified Proth prime `1314883·2^128 + 1 ≈ 2^148.33`. -/
abbrev P : ℕ := 447431499464104329654112393943705681183899649

private theorem pow_two_pow_succ {M : Type} [Monoid M] (a : M) (k : ℕ) :
    a ^ (2:ℕ) ^ (k + 1) = (a ^ (2:ℕ) ^ k) ^ 2 := by
  rw [← pow_mul]
  congr 1

/-! ### The `t`-chain: `t_k = 3^(2^k)` in `ZMod P` -/

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
      422746358962007218968492329501206501279098621 := by
  rw [pow_two_pow_succ, t6]; decide
private theorem t8 :
    (3 : ZMod P) ^ (2:ℕ) ^ 8 =
      203419822850326010437911171957718044730935926 := by
  rw [pow_two_pow_succ, t7]; decide
private theorem t9 :
    (3 : ZMod P) ^ (2:ℕ) ^ 9 =
      231069243294191346427293477666927137565760760 := by
  rw [pow_two_pow_succ, t8]; decide
private theorem t10 :
    (3 : ZMod P) ^ (2:ℕ) ^ 10 =
      320808521741997842210732791538568894212992929 := by
  rw [pow_two_pow_succ, t9]; decide
private theorem t11 :
    (3 : ZMod P) ^ (2:ℕ) ^ 11 =
      404549356045461909963258633204037147427853812 := by
  rw [pow_two_pow_succ, t10]; decide
private theorem t12 :
    (3 : ZMod P) ^ (2:ℕ) ^ 12 =
      364436964318164385587275694857480193840844331 := by
  rw [pow_two_pow_succ, t11]; decide
private theorem t13 :
    (3 : ZMod P) ^ (2:ℕ) ^ 13 =
      223806042917663044706417324635788220382386997 := by
  rw [pow_two_pow_succ, t12]; decide
private theorem t14 :
    (3 : ZMod P) ^ (2:ℕ) ^ 14 =
      393302773253737280447770666149734680777757096 := by
  rw [pow_two_pow_succ, t13]; decide
private theorem t15 :
    (3 : ZMod P) ^ (2:ℕ) ^ 15 =
      291593792584074777557496831913673450545054943 := by
  rw [pow_two_pow_succ, t14]; decide
private theorem t16 :
    (3 : ZMod P) ^ (2:ℕ) ^ 16 =
      103616758939625877423375962420539366192513498 := by
  rw [pow_two_pow_succ, t15]; decide
private theorem t17 :
    (3 : ZMod P) ^ (2:ℕ) ^ 17 =
      169201827415136858927524896410686081294538760 := by
  rw [pow_two_pow_succ, t16]; decide
private theorem t18 :
    (3 : ZMod P) ^ (2:ℕ) ^ 18 =
      19238685022527868481846970449437075707949402 := by
  rw [pow_two_pow_succ, t17]; decide
private theorem t19 :
    (3 : ZMod P) ^ (2:ℕ) ^ 19 =
      132588873314950080412496248856654402976274484 := by
  rw [pow_two_pow_succ, t18]; decide
private theorem t20 :
    (3 : ZMod P) ^ (2:ℕ) ^ 20 =
      102613594694253304222509222930043761477265267 := by
  rw [pow_two_pow_succ, t19]; decide
private theorem t21 :
    (3 : ZMod P) ^ (2:ℕ) ^ 21 =
      260523346499763436617330526209603720946215281 := by
  rw [pow_two_pow_succ, t20]; decide
private theorem t22 :
    (3 : ZMod P) ^ (2:ℕ) ^ 22 =
      93737602562617968330340102831386827904037753 := by
  rw [pow_two_pow_succ, t21]; decide
private theorem t23 :
    (3 : ZMod P) ^ (2:ℕ) ^ 23 =
      113243340354907475391027295906418260791901659 := by
  rw [pow_two_pow_succ, t22]; decide
private theorem t24 :
    (3 : ZMod P) ^ (2:ℕ) ^ 24 =
      119206574729454160721007384989012718557770954 := by
  rw [pow_two_pow_succ, t23]; decide
private theorem t25 :
    (3 : ZMod P) ^ (2:ℕ) ^ 25 =
      343664071397274190148005317683062684722244399 := by
  rw [pow_two_pow_succ, t24]; decide
private theorem t26 :
    (3 : ZMod P) ^ (2:ℕ) ^ 26 =
      98280463518922520294612534958747651359201913 := by
  rw [pow_two_pow_succ, t25]; decide
private theorem t27 :
    (3 : ZMod P) ^ (2:ℕ) ^ 27 =
      262866928334650027530795530486923370866106170 := by
  rw [pow_two_pow_succ, t26]; decide
private theorem t28 :
    (3 : ZMod P) ^ (2:ℕ) ^ 28 =
      241226602685442852047807337206197876045089449 := by
  rw [pow_two_pow_succ, t27]; decide
private theorem t29 :
    (3 : ZMod P) ^ (2:ℕ) ^ 29 =
      61636289159399149649933126578560033216551546 := by
  rw [pow_two_pow_succ, t28]; decide
private theorem t30 :
    (3 : ZMod P) ^ (2:ℕ) ^ 30 =
      421403582623832930817117871283815312321352694 := by
  rw [pow_two_pow_succ, t29]; decide
private theorem t31 :
    (3 : ZMod P) ^ (2:ℕ) ^ 31 =
      95653114166121137493197171926711409665112869 := by
  rw [pow_two_pow_succ, t30]; decide
private theorem t32 :
    (3 : ZMod P) ^ (2:ℕ) ^ 32 =
      169067153080630103291994410968642705157852608 := by
  rw [pow_two_pow_succ, t31]; decide
private theorem t33 :
    (3 : ZMod P) ^ (2:ℕ) ^ 33 =
      77243870089713211406277717909101286517353669 := by
  rw [pow_two_pow_succ, t32]; decide
private theorem t34 :
    (3 : ZMod P) ^ (2:ℕ) ^ 34 =
      420794047990975970148680428763245657800535646 := by
  rw [pow_two_pow_succ, t33]; decide
private theorem t35 :
    (3 : ZMod P) ^ (2:ℕ) ^ 35 =
      209042597017020679366266678942606827376377214 := by
  rw [pow_two_pow_succ, t34]; decide
private theorem t36 :
    (3 : ZMod P) ^ (2:ℕ) ^ 36 =
      16768680447432537042055410710106691746650324 := by
  rw [pow_two_pow_succ, t35]; decide
private theorem t37 :
    (3 : ZMod P) ^ (2:ℕ) ^ 37 =
      125185685800841154134303967874717017657099798 := by
  rw [pow_two_pow_succ, t36]; decide
private theorem t38 :
    (3 : ZMod P) ^ (2:ℕ) ^ 38 =
      5335299064467274913496079279275181914495420 := by
  rw [pow_two_pow_succ, t37]; decide
private theorem t39 :
    (3 : ZMod P) ^ (2:ℕ) ^ 39 =
      376893964349639427286427568073107662855139639 := by
  rw [pow_two_pow_succ, t38]; decide
private theorem t40 :
    (3 : ZMod P) ^ (2:ℕ) ^ 40 =
      368809748013201351117129699036166614989475220 := by
  rw [pow_two_pow_succ, t39]; decide
private theorem t41 :
    (3 : ZMod P) ^ (2:ℕ) ^ 41 =
      340019453391004455543857770993672771468890108 := by
  rw [pow_two_pow_succ, t40]; decide
private theorem t42 :
    (3 : ZMod P) ^ (2:ℕ) ^ 42 =
      359213313349673256835720456827489509737350764 := by
  rw [pow_two_pow_succ, t41]; decide
private theorem t43 :
    (3 : ZMod P) ^ (2:ℕ) ^ 43 =
      131911974908571934139864054064171721653053885 := by
  rw [pow_two_pow_succ, t42]; decide
private theorem t44 :
    (3 : ZMod P) ^ (2:ℕ) ^ 44 =
      114432051246240668425771717126264476146034055 := by
  rw [pow_two_pow_succ, t43]; decide
private theorem t45 :
    (3 : ZMod P) ^ (2:ℕ) ^ 45 =
      46077672874598536323169886903094294326546804 := by
  rw [pow_two_pow_succ, t44]; decide
private theorem t46 :
    (3 : ZMod P) ^ (2:ℕ) ^ 46 =
      367306148686014983646280707045747634343410810 := by
  rw [pow_two_pow_succ, t45]; decide
private theorem t47 :
    (3 : ZMod P) ^ (2:ℕ) ^ 47 =
      11190992222439088154697554955841001785326360 := by
  rw [pow_two_pow_succ, t46]; decide
private theorem t48 :
    (3 : ZMod P) ^ (2:ℕ) ^ 48 =
      362184982489751993705263028188425435827300474 := by
  rw [pow_two_pow_succ, t47]; decide
private theorem t49 :
    (3 : ZMod P) ^ (2:ℕ) ^ 49 =
      268136588550598297055859759432834341362440658 := by
  rw [pow_two_pow_succ, t48]; decide
private theorem t50 :
    (3 : ZMod P) ^ (2:ℕ) ^ 50 =
      412204804330429155738887471834534774941067731 := by
  rw [pow_two_pow_succ, t49]; decide
private theorem t51 :
    (3 : ZMod P) ^ (2:ℕ) ^ 51 =
      260277570820764191132991482052029346710151331 := by
  rw [pow_two_pow_succ, t50]; decide
private theorem t52 :
    (3 : ZMod P) ^ (2:ℕ) ^ 52 =
      17546500734154617595509774306060004491663408 := by
  rw [pow_two_pow_succ, t51]; decide
private theorem t53 :
    (3 : ZMod P) ^ (2:ℕ) ^ 53 =
      324770482180544827055983669681519814454034841 := by
  rw [pow_two_pow_succ, t52]; decide
private theorem t54 :
    (3 : ZMod P) ^ (2:ℕ) ^ 54 =
      157096218959096424292178767465230314517081618 := by
  rw [pow_two_pow_succ, t53]; decide
private theorem t55 :
    (3 : ZMod P) ^ (2:ℕ) ^ 55 =
      307044280261019468843543842816959890095173845 := by
  rw [pow_two_pow_succ, t54]; decide
private theorem t56 :
    (3 : ZMod P) ^ (2:ℕ) ^ 56 =
      198931269137567465391316304285782845211665529 := by
  rw [pow_two_pow_succ, t55]; decide
private theorem t57 :
    (3 : ZMod P) ^ (2:ℕ) ^ 57 =
      105341537733106843107920215801578693170238407 := by
  rw [pow_two_pow_succ, t56]; decide
private theorem t58 :
    (3 : ZMod P) ^ (2:ℕ) ^ 58 =
      45579306075195577514420753700052422317323772 := by
  rw [pow_two_pow_succ, t57]; decide
private theorem t59 :
    (3 : ZMod P) ^ (2:ℕ) ^ 59 =
      186458555951956785845636632515310677876246861 := by
  rw [pow_two_pow_succ, t58]; decide
private theorem t60 :
    (3 : ZMod P) ^ (2:ℕ) ^ 60 =
      160297538345304859731848132414255863053046804 := by
  rw [pow_two_pow_succ, t59]; decide
private theorem t61 :
    (3 : ZMod P) ^ (2:ℕ) ^ 61 =
      154341786774854804088692383606526314616215245 := by
  rw [pow_two_pow_succ, t60]; decide
private theorem t62 :
    (3 : ZMod P) ^ (2:ℕ) ^ 62 =
      259503891733105987416242008482317983982276872 := by
  rw [pow_two_pow_succ, t61]; decide
private theorem t63 :
    (3 : ZMod P) ^ (2:ℕ) ^ 63 =
      175512152244087630460658606385448750538426206 := by
  rw [pow_two_pow_succ, t62]; decide
private theorem t64 :
    (3 : ZMod P) ^ (2:ℕ) ^ 64 =
      1313460066848586486293782897583157629987413 := by
  rw [pow_two_pow_succ, t63]; decide
private theorem t65 :
    (3 : ZMod P) ^ (2:ℕ) ^ 65 =
      424387306733335107639096064612055224103150121 := by
  rw [pow_two_pow_succ, t64]; decide
private theorem t66 :
    (3 : ZMod P) ^ (2:ℕ) ^ 66 =
      446631406309209701015048786279157174972028886 := by
  rw [pow_two_pow_succ, t65]; decide
private theorem t67 :
    (3 : ZMod P) ^ (2:ℕ) ^ 67 =
      287843424884372001409372368814257572563045980 := by
  rw [pow_two_pow_succ, t66]; decide
private theorem t68 :
    (3 : ZMod P) ^ (2:ℕ) ^ 68 =
      340080270142034284095329535760791016796589047 := by
  rw [pow_two_pow_succ, t67]; decide
private theorem t69 :
    (3 : ZMod P) ^ (2:ℕ) ^ 69 =
      350737445317512644739372743093866300481463953 := by
  rw [pow_two_pow_succ, t68]; decide
private theorem t70 :
    (3 : ZMod P) ^ (2:ℕ) ^ 70 =
      37872868691287865069494303452502056359026676 := by
  rw [pow_two_pow_succ, t69]; decide
private theorem t71 :
    (3 : ZMod P) ^ (2:ℕ) ^ 71 =
      403845222767008437659732020977207432428577231 := by
  rw [pow_two_pow_succ, t70]; decide
private theorem t72 :
    (3 : ZMod P) ^ (2:ℕ) ^ 72 =
      321734593391688683943817841784307238279749525 := by
  rw [pow_two_pow_succ, t71]; decide
private theorem t73 :
    (3 : ZMod P) ^ (2:ℕ) ^ 73 =
      229082030574674170654398291716919011642598917 := by
  rw [pow_two_pow_succ, t72]; decide
private theorem t74 :
    (3 : ZMod P) ^ (2:ℕ) ^ 74 =
      11845157657110629349190248452692379381836903 := by
  rw [pow_two_pow_succ, t73]; decide
private theorem t75 :
    (3 : ZMod P) ^ (2:ℕ) ^ 75 =
      28120698999700253040931598462158168777068881 := by
  rw [pow_two_pow_succ, t74]; decide
private theorem t76 :
    (3 : ZMod P) ^ (2:ℕ) ^ 76 =
      329709462997224189864877100144989900902005223 := by
  rw [pow_two_pow_succ, t75]; decide
private theorem t77 :
    (3 : ZMod P) ^ (2:ℕ) ^ 77 =
      128258342116760254526700193700211483108179590 := by
  rw [pow_two_pow_succ, t76]; decide
private theorem t78 :
    (3 : ZMod P) ^ (2:ℕ) ^ 78 =
      222534797242373526391925284281973655111234468 := by
  rw [pow_two_pow_succ, t77]; decide
private theorem t79 :
    (3 : ZMod P) ^ (2:ℕ) ^ 79 =
      394203929433025118184803742938894409950768448 := by
  rw [pow_two_pow_succ, t78]; decide
private theorem t80 :
    (3 : ZMod P) ^ (2:ℕ) ^ 80 =
      35533171025109333804361559144181365230117214 := by
  rw [pow_two_pow_succ, t79]; decide
private theorem t81 :
    (3 : ZMod P) ^ (2:ℕ) ^ 81 =
      76237714584847380944773288300956378574947384 := by
  rw [pow_two_pow_succ, t80]; decide
private theorem t82 :
    (3 : ZMod P) ^ (2:ℕ) ^ 82 =
      355373741491676854826454792194861920122733855 := by
  rw [pow_two_pow_succ, t81]; decide
private theorem t83 :
    (3 : ZMod P) ^ (2:ℕ) ^ 83 =
      286860834877949481915416735488866689361224569 := by
  rw [pow_two_pow_succ, t82]; decide
private theorem t84 :
    (3 : ZMod P) ^ (2:ℕ) ^ 84 =
      311511430341107957532976265004716031481797749 := by
  rw [pow_two_pow_succ, t83]; decide
private theorem t85 :
    (3 : ZMod P) ^ (2:ℕ) ^ 85 =
      325488395250331979876984028338365584468161285 := by
  rw [pow_two_pow_succ, t84]; decide
private theorem t86 :
    (3 : ZMod P) ^ (2:ℕ) ^ 86 =
      192281722869190655023445006561160812996399601 := by
  rw [pow_two_pow_succ, t85]; decide
private theorem t87 :
    (3 : ZMod P) ^ (2:ℕ) ^ 87 =
      298574492168287740615709831961295712145714828 := by
  rw [pow_two_pow_succ, t86]; decide
private theorem t88 :
    (3 : ZMod P) ^ (2:ℕ) ^ 88 =
      288813407662113936604767880146747395933835314 := by
  rw [pow_two_pow_succ, t87]; decide
private theorem t89 :
    (3 : ZMod P) ^ (2:ℕ) ^ 89 =
      444492184291319387522773765592634796706809396 := by
  rw [pow_two_pow_succ, t88]; decide
private theorem t90 :
    (3 : ZMod P) ^ (2:ℕ) ^ 90 =
      371437411135412370350871588444116354821937563 := by
  rw [pow_two_pow_succ, t89]; decide
private theorem t91 :
    (3 : ZMod P) ^ (2:ℕ) ^ 91 =
      124234053445669052538115293565967597235741004 := by
  rw [pow_two_pow_succ, t90]; decide
private theorem t92 :
    (3 : ZMod P) ^ (2:ℕ) ^ 92 =
      109715983432109302160593881829984508313888446 := by
  rw [pow_two_pow_succ, t91]; decide
private theorem t93 :
    (3 : ZMod P) ^ (2:ℕ) ^ 93 =
      75511693315023898854826077281795080915282180 := by
  rw [pow_two_pow_succ, t92]; decide
private theorem t94 :
    (3 : ZMod P) ^ (2:ℕ) ^ 94 =
      432068856915298442992171698090157750134058397 := by
  rw [pow_two_pow_succ, t93]; decide
private theorem t95 :
    (3 : ZMod P) ^ (2:ℕ) ^ 95 =
      2969571292199460468013161226793323562338436 := by
  rw [pow_two_pow_succ, t94]; decide
private theorem t96 :
    (3 : ZMod P) ^ (2:ℕ) ^ 96 =
      252385167727232767379338692510978360839328477 := by
  rw [pow_two_pow_succ, t95]; decide
private theorem t97 :
    (3 : ZMod P) ^ (2:ℕ) ^ 97 =
      193579651289769742652204151423966519769177733 := by
  rw [pow_two_pow_succ, t96]; decide
private theorem t98 :
    (3 : ZMod P) ^ (2:ℕ) ^ 98 =
      25453593922435717241021018581015100472282480 := by
  rw [pow_two_pow_succ, t97]; decide
private theorem t99 :
    (3 : ZMod P) ^ (2:ℕ) ^ 99 =
      134597972318002151909442890677133713788359531 := by
  rw [pow_two_pow_succ, t98]; decide
private theorem t100 :
    (3 : ZMod P) ^ (2:ℕ) ^ 100 =
      40380901824690351148318666465404630423381221 := by
  rw [pow_two_pow_succ, t99]; decide
private theorem t101 :
    (3 : ZMod P) ^ (2:ℕ) ^ 101 =
      354157171993534922066673562354921413794910851 := by
  rw [pow_two_pow_succ, t100]; decide
private theorem t102 :
    (3 : ZMod P) ^ (2:ℕ) ^ 102 =
      399341855381576737186886326767991070330908659 := by
  rw [pow_two_pow_succ, t101]; decide
private theorem t103 :
    (3 : ZMod P) ^ (2:ℕ) ^ 103 =
      89271810642999276540320150401578137771316699 := by
  rw [pow_two_pow_succ, t102]; decide
private theorem t104 :
    (3 : ZMod P) ^ (2:ℕ) ^ 104 =
      416992468267123100332087158338663977949291850 := by
  rw [pow_two_pow_succ, t103]; decide
private theorem t105 :
    (3 : ZMod P) ^ (2:ℕ) ^ 105 =
      151065483109157085819208261224168673816138706 := by
  rw [pow_two_pow_succ, t104]; decide
private theorem t106 :
    (3 : ZMod P) ^ (2:ℕ) ^ 106 =
      443886683359896188645529509645847759952641617 := by
  rw [pow_two_pow_succ, t105]; decide
private theorem t107 :
    (3 : ZMod P) ^ (2:ℕ) ^ 107 =
      54525542066478537181965051364206032903983843 := by
  rw [pow_two_pow_succ, t106]; decide
private theorem t108 :
    (3 : ZMod P) ^ (2:ℕ) ^ 108 =
      87891210078299250102378437525400346059058530 := by
  rw [pow_two_pow_succ, t107]; decide
private theorem t109 :
    (3 : ZMod P) ^ (2:ℕ) ^ 109 =
      402961310614187703925752499552960272725094994 := by
  rw [pow_two_pow_succ, t108]; decide
private theorem t110 :
    (3 : ZMod P) ^ (2:ℕ) ^ 110 =
      238857429315380053819992637816111470518482108 := by
  rw [pow_two_pow_succ, t109]; decide
private theorem t111 :
    (3 : ZMod P) ^ (2:ℕ) ^ 111 =
      291180247641164614490935700831086576294985203 := by
  rw [pow_two_pow_succ, t110]; decide
private theorem t112 :
    (3 : ZMod P) ^ (2:ℕ) ^ 112 =
      23368663201168259163060389912309162073406317 := by
  rw [pow_two_pow_succ, t111]; decide
private theorem t113 :
    (3 : ZMod P) ^ (2:ℕ) ^ 113 =
      242217766506915500785192515734973151708176189 := by
  rw [pow_two_pow_succ, t112]; decide
private theorem t114 :
    (3 : ZMod P) ^ (2:ℕ) ^ 114 =
      433520082127100381178178871897948784231511736 := by
  rw [pow_two_pow_succ, t113]; decide
private theorem t115 :
    (3 : ZMod P) ^ (2:ℕ) ^ 115 =
      289924075901613571893828565691867660014846760 := by
  rw [pow_two_pow_succ, t114]; decide
private theorem t116 :
    (3 : ZMod P) ^ (2:ℕ) ^ 116 =
      215896730436162566560049700573813837492678737 := by
  rw [pow_two_pow_succ, t115]; decide
private theorem t117 :
    (3 : ZMod P) ^ (2:ℕ) ^ 117 =
      123439630093512213352149161169059933269544409 := by
  rw [pow_two_pow_succ, t116]; decide
private theorem t118 :
    (3 : ZMod P) ^ (2:ℕ) ^ 118 =
      191999816305023964399459922743567779006009964 := by
  rw [pow_two_pow_succ, t117]; decide
private theorem t119 :
    (3 : ZMod P) ^ (2:ℕ) ^ 119 =
      222154240626651163158863664875462407363096382 := by
  rw [pow_two_pow_succ, t118]; decide
private theorem t120 :
    (3 : ZMod P) ^ (2:ℕ) ^ 120 =
      251247791017542228129283653318562186382031489 := by
  rw [pow_two_pow_succ, t119]; decide
private theorem t121 :
    (3 : ZMod P) ^ (2:ℕ) ^ 121 =
      127987351028553136213851140754948961601470436 := by
  rw [pow_two_pow_succ, t120]; decide
private theorem t122 :
    (3 : ZMod P) ^ (2:ℕ) ^ 122 =
      35687863708773025594434249324854631100806907 := by
  rw [pow_two_pow_succ, t121]; decide
private theorem t123 :
    (3 : ZMod P) ^ (2:ℕ) ^ 123 =
      188055957394639171088163647372167390522577150 := by
  rw [pow_two_pow_succ, t122]; decide
private theorem t124 :
    (3 : ZMod P) ^ (2:ℕ) ^ 124 =
      2435551916248223399629432719004037572582143 := by
  rw [pow_two_pow_succ, t123]; decide
private theorem t125 :
    (3 : ZMod P) ^ (2:ℕ) ^ 125 =
      215213828568810627866951359774646618302712651 := by
  rw [pow_two_pow_succ, t124]; decide
private theorem t126 :
    (3 : ZMod P) ^ (2:ℕ) ^ 126 =
      143962766386992572906643047804727094543313881 := by
  rw [pow_two_pow_succ, t125]; decide
private theorem t127 :
    (3 : ZMod P) ^ (2:ℕ) ^ 127 =
      373526801282806997056678508833983488853943928 := by
  rw [pow_two_pow_succ, t126]; decide
private theorem t128 :
    (3 : ZMod P) ^ (2:ℕ) ^ 128 =
      322876877735545241561215717232733891676484088 := by
  rw [pow_two_pow_succ, t127]; decide

/-! ### `x = 3^1314883` (binary: `2^20 + 2^18 + 2^12 + 2^6 + 2^1 + 2^0`) -/

private theorem hx :
    (3 : ZMod P) ^ (1314883:ℕ) =
      280171030852096594497184040840251869585814495 := by
  rw [show (1314883:ℕ) = 2^20 + 2^18 + 2^12 + 2^6 + 2^1 + 2^0 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, t20, t18, t12, t6, t1, t0]
  decide

/-! ### The `u`-chain: `u_k = x^(2^k)` -/

private theorem u0 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 0 =
      280171030852096594497184040840251869585814495 := by
  norm_num
private theorem u1 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 1 =
      408799341497520488023713579796048135799379179 := by
  rw [pow_two_pow_succ, u0]; decide
private theorem u2 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 2 =
      75386045048101410062365513178758387470844874 := by
  rw [pow_two_pow_succ, u1]; decide
private theorem u3 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 3 =
      298993459080667736672003670079643130035089305 := by
  rw [pow_two_pow_succ, u2]; decide
private theorem u4 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 4 =
      405168257448116237693482156872127802727265360 := by
  rw [pow_two_pow_succ, u3]; decide
private theorem u5 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 5 =
      234498273270250947304992727894814893665405453 := by
  rw [pow_two_pow_succ, u4]; decide
private theorem u6 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 6 =
      139248752423515024992262649665521820614620230 := by
  rw [pow_two_pow_succ, u5]; decide
private theorem u7 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 7 =
      366253689854960219259751567950842764200477388 := by
  rw [pow_two_pow_succ, u6]; decide
private theorem u8 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 8 =
      142190466237217053303740365433577400648399293 := by
  rw [pow_two_pow_succ, u7]; decide
private theorem u9 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 9 =
      89957560272287268519278557655929515597690204 := by
  rw [pow_two_pow_succ, u8]; decide
private theorem u10 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 10 =
      66125629424386155176163721700940779127114939 := by
  rw [pow_two_pow_succ, u9]; decide
private theorem u11 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 11 =
      74639792207360161157813133861084484592311850 := by
  rw [pow_two_pow_succ, u10]; decide
private theorem u12 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 12 =
      239370074955946410068763664363396592324799164 := by
  rw [pow_two_pow_succ, u11]; decide
private theorem u13 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 13 =
      23034152891557938402199672885748925676443147 := by
  rw [pow_two_pow_succ, u12]; decide
private theorem u14 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 14 =
      207436412382324925636529962664202493041879 := by
  rw [pow_two_pow_succ, u13]; decide
private theorem u15 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 15 =
      429911970629804686477369242444390240838561505 := by
  rw [pow_two_pow_succ, u14]; decide
private theorem u16 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 16 =
      404084316408707291243506077578848145544841740 := by
  rw [pow_two_pow_succ, u15]; decide
private theorem u17 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 17 =
      311988420111636642132649127593100872185107659 := by
  rw [pow_two_pow_succ, u16]; decide
private theorem u18 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 18 =
      80961978772415429861404574723980102274424594 := by
  rw [pow_two_pow_succ, u17]; decide
private theorem u19 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 19 =
      75791602059413691393733278475756369764331492 := by
  rw [pow_two_pow_succ, u18]; decide
private theorem u20 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 20 =
      39800480814891694191680904275703834751699189 := by
  rw [pow_two_pow_succ, u19]; decide
private theorem u21 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 21 =
      122716027048261257953908205347961230445882791 := by
  rw [pow_two_pow_succ, u20]; decide
private theorem u22 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 22 =
      151578233192612596489818333327772254491097555 := by
  rw [pow_two_pow_succ, u21]; decide
private theorem u23 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 23 =
      222517535436973076530505791904861259982828172 := by
  rw [pow_two_pow_succ, u22]; decide
private theorem u24 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 24 =
      96000053367477934550750776426122367346283836 := by
  rw [pow_two_pow_succ, u23]; decide
private theorem u25 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 25 =
      383231027723656894786716489724386917632829342 := by
  rw [pow_two_pow_succ, u24]; decide
private theorem u26 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 26 =
      406359713704697673085394347593489935853613860 := by
  rw [pow_two_pow_succ, u25]; decide
private theorem u27 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 27 =
      298967196182908239856517014732574398560031033 := by
  rw [pow_two_pow_succ, u26]; decide
private theorem u28 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 28 =
      22186986927182472489551657497578089179478535 := by
  rw [pow_two_pow_succ, u27]; decide
private theorem u29 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 29 =
      400502783141700828607168343076153681580633327 := by
  rw [pow_two_pow_succ, u28]; decide
private theorem u30 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 30 =
      213970204572591272118540514199387823314757697 := by
  rw [pow_two_pow_succ, u29]; decide
private theorem u31 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 31 =
      178616885622583169848986488971149341966469955 := by
  rw [pow_two_pow_succ, u30]; decide
private theorem u32 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 32 =
      157100995053170658433433294225456711720249391 := by
  rw [pow_two_pow_succ, u31]; decide
private theorem u33 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 33 =
      439290758871423740197232825675092502361014922 := by
  rw [pow_two_pow_succ, u32]; decide
private theorem u34 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 34 =
      396064726945311111155986154981158977938184548 := by
  rw [pow_two_pow_succ, u33]; decide
private theorem u35 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 35 =
      278518456258873963086604488583220059660418690 := by
  rw [pow_two_pow_succ, u34]; decide
private theorem u36 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 36 =
      438222526366913487539454580100586877759335053 := by
  rw [pow_two_pow_succ, u35]; decide
private theorem u37 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 37 =
      292655977414177481135449940381072688863263231 := by
  rw [pow_two_pow_succ, u36]; decide
private theorem u38 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 38 =
      411043690539182749947757193831510298744685442 := by
  rw [pow_two_pow_succ, u37]; decide
private theorem u39 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 39 =
      154656577821958775775521681550526701468379834 := by
  rw [pow_two_pow_succ, u38]; decide
private theorem u40 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 40 =
      376341331971606645061404739929398495522461917 := by
  rw [pow_two_pow_succ, u39]; decide
private theorem u41 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 41 =
      172122676109574109385246577527102786157908871 := by
  rw [pow_two_pow_succ, u40]; decide
private theorem u42 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 42 =
      233741352534100594041950946559808870353441543 := by
  rw [pow_two_pow_succ, u41]; decide
private theorem u43 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 43 =
      349984985708176410450658772475167528246163119 := by
  rw [pow_two_pow_succ, u42]; decide
private theorem u44 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 44 =
      109381218857098492242244691220621274944669179 := by
  rw [pow_two_pow_succ, u43]; decide
private theorem u45 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 45 =
      323486353701790577905076196529649245602919572 := by
  rw [pow_two_pow_succ, u44]; decide
private theorem u46 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 46 =
      42000104101078233696326221492334920205981159 := by
  rw [pow_two_pow_succ, u45]; decide
private theorem u47 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 47 =
      401643974929623328739205375253412112898438167 := by
  rw [pow_two_pow_succ, u46]; decide
private theorem u48 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 48 =
      172075441671150901521406070896857223699320252 := by
  rw [pow_two_pow_succ, u47]; decide
private theorem u49 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 49 =
      89165168894966293864051394846045018267044438 := by
  rw [pow_two_pow_succ, u48]; decide
private theorem u50 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 50 =
      369849366531871359028001612670919744543693807 := by
  rw [pow_two_pow_succ, u49]; decide
private theorem u51 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 51 =
      82990616551468137468133818641090219571176853 := by
  rw [pow_two_pow_succ, u50]; decide
private theorem u52 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 52 =
      411256734351298359037115046804228983883761249 := by
  rw [pow_two_pow_succ, u51]; decide
private theorem u53 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 53 =
      131830839825918015614343534649934902616091872 := by
  rw [pow_two_pow_succ, u52]; decide
private theorem u54 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 54 =
      162795148248719271839105897456000944392096362 := by
  rw [pow_two_pow_succ, u53]; decide
private theorem u55 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 55 =
      318958332066038085834150221319052020730363983 := by
  rw [pow_two_pow_succ, u54]; decide
private theorem u56 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 56 =
      345752016639164987648261587646880319677323200 := by
  rw [pow_two_pow_succ, u55]; decide
private theorem u57 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 57 =
      414546412565975499816088267488486867560829551 := by
  rw [pow_two_pow_succ, u56]; decide
private theorem u58 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 58 =
      70205346271597301729728884749292733027734192 := by
  rw [pow_two_pow_succ, u57]; decide
private theorem u59 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 59 =
      426739838696623971181886150315488046347239745 := by
  rw [pow_two_pow_succ, u58]; decide
private theorem u60 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 60 =
      274399210119864375817170684844123482779832018 := by
  rw [pow_two_pow_succ, u59]; decide
private theorem u61 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 61 =
      119053167181374543395552861274044248311675116 := by
  rw [pow_two_pow_succ, u60]; decide
private theorem u62 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 62 =
      412719748849744554713079777632327472331046110 := by
  rw [pow_two_pow_succ, u61]; decide
private theorem u63 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 63 =
      393826967133456700306857007881325074827890369 := by
  rw [pow_two_pow_succ, u62]; decide
private theorem u64 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 64 =
      45594332118817529296465701186096874521298158 := by
  rw [pow_two_pow_succ, u63]; decide
private theorem u65 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 65 =
      56488219374928317362321035343885477622279796 := by
  rw [pow_two_pow_succ, u64]; decide
private theorem u66 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 66 =
      159971252945889691163482731837851419710077383 := by
  rw [pow_two_pow_succ, u65]; decide
private theorem u67 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 67 =
      397601185186196185581063850512800740635875211 := by
  rw [pow_two_pow_succ, u66]; decide
private theorem u68 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 68 =
      441938641616214229540485175833849030027802114 := by
  rw [pow_two_pow_succ, u67]; decide
private theorem u69 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 69 =
      330862394637675634288927063272775000963164978 := by
  rw [pow_two_pow_succ, u68]; decide
private theorem u70 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 70 =
      63284370928090495680808389926814975455913282 := by
  rw [pow_two_pow_succ, u69]; decide
private theorem u71 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 71 =
      316470608200097799412967458660722536409700124 := by
  rw [pow_two_pow_succ, u70]; decide
private theorem u72 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 72 =
      153737363407352417152334451403955841909745874 := by
  rw [pow_two_pow_succ, u71]; decide
private theorem u73 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 73 =
      87828433299450265734548575682684652990621532 := by
  rw [pow_two_pow_succ, u72]; decide
private theorem u74 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 74 =
      166708597332189237337166589458697197173513412 := by
  rw [pow_two_pow_succ, u73]; decide
private theorem u75 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 75 =
      431780608238132975765143302111646048522772696 := by
  rw [pow_two_pow_succ, u74]; decide
private theorem u76 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 76 =
      363532122712160635736953370325702285143182924 := by
  rw [pow_two_pow_succ, u75]; decide
private theorem u77 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 77 =
      223292973462097531632786116186818305311021428 := by
  rw [pow_two_pow_succ, u76]; decide
private theorem u78 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 78 =
      384904563762418581312872304865615222541596507 := by
  rw [pow_two_pow_succ, u77]; decide
private theorem u79 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 79 =
      262703175471342415625968666404152803464830516 := by
  rw [pow_two_pow_succ, u78]; decide
private theorem u80 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 80 =
      415813533277702100243528151502683106269141824 := by
  rw [pow_two_pow_succ, u79]; decide
private theorem u81 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 81 =
      331585594911069371302681831888913454761839365 := by
  rw [pow_two_pow_succ, u80]; decide
private theorem u82 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 82 =
      426683545269509815348708146047352955577321803 := by
  rw [pow_two_pow_succ, u81]; decide
private theorem u83 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 83 =
      169554421181975374866581096661749237184617351 := by
  rw [pow_two_pow_succ, u82]; decide
private theorem u84 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 84 =
      59566309403135930461138506298250297410726992 := by
  rw [pow_two_pow_succ, u83]; decide
private theorem u85 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 85 =
      326842365840156405560401341825996538269448470 := by
  rw [pow_two_pow_succ, u84]; decide
private theorem u86 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 86 =
      371307167754237129322016795919840746575753366 := by
  rw [pow_two_pow_succ, u85]; decide
private theorem u87 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 87 =
      317846562155517377424276111357348012426738508 := by
  rw [pow_two_pow_succ, u86]; decide
private theorem u88 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 88 =
      370841030058852589070075939158912300237947623 := by
  rw [pow_two_pow_succ, u87]; decide
private theorem u89 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 89 =
      10378721536521731457416975122510821209114215 := by
  rw [pow_two_pow_succ, u88]; decide
private theorem u90 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 90 =
      48161525498002750001599698839705139549054068 := by
  rw [pow_two_pow_succ, u89]; decide
private theorem u91 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 91 =
      333409700458781619953023529283301331588237429 := by
  rw [pow_two_pow_succ, u90]; decide
private theorem u92 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 92 =
      426506245569861032695100917698477886141008840 := by
  rw [pow_two_pow_succ, u91]; decide
private theorem u93 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 93 =
      115323529695882095912511143252800121786904555 := by
  rw [pow_two_pow_succ, u92]; decide
private theorem u94 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 94 =
      51291875658245077831113765107467670595855271 := by
  rw [pow_two_pow_succ, u93]; decide
private theorem u95 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 95 =
      286774094421011207972857073349361973465068540 := by
  rw [pow_two_pow_succ, u94]; decide
private theorem u96 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 96 =
      221040384294903227516270382163481419401903948 := by
  rw [pow_two_pow_succ, u95]; decide
private theorem u97 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 97 =
      78208724888538726549596958111066183775166594 := by
  rw [pow_two_pow_succ, u96]; decide
private theorem u98 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 98 =
      71142380506893092109472467839359761415989182 := by
  rw [pow_two_pow_succ, u97]; decide
private theorem u99 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 99 =
      117472479164680558729637673327678943766183273 := by
  rw [pow_two_pow_succ, u98]; decide
private theorem u100 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 100 =
      362426171976865471282550327095015913487026374 := by
  rw [pow_two_pow_succ, u99]; decide
private theorem u101 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 101 =
      329257590534887869644986719935102025348055548 := by
  rw [pow_two_pow_succ, u100]; decide
private theorem u102 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 102 =
      68392228017522835421309041020814802560930532 := by
  rw [pow_two_pow_succ, u101]; decide
private theorem u103 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 103 =
      426499655677044837342063317367391226571521364 := by
  rw [pow_two_pow_succ, u102]; decide
private theorem u104 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 104 =
      9425476629379217439692591051035470611729681 := by
  rw [pow_two_pow_succ, u103]; decide
private theorem u105 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 105 =
      414551160958561336498516429087048488955350285 := by
  rw [pow_two_pow_succ, u104]; decide
private theorem u106 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 106 =
      279525286669304306876713901928870100829725247 := by
  rw [pow_two_pow_succ, u105]; decide
private theorem u107 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 107 =
      379709901819216778025113480844623111020597944 := by
  rw [pow_two_pow_succ, u106]; decide
private theorem u108 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 108 =
      374472941452272419355143689929491699970415794 := by
  rw [pow_two_pow_succ, u107]; decide
private theorem u109 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 109 =
      292258200384037034593084938348931496567085233 := by
  rw [pow_two_pow_succ, u108]; decide
private theorem u110 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 110 =
      437159741639270235908088508838462369198294729 := by
  rw [pow_two_pow_succ, u109]; decide
private theorem u111 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 111 =
      181797433116677671044030981227236596490366749 := by
  rw [pow_two_pow_succ, u110]; decide
private theorem u112 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 112 =
      218437325673519553618538344592653650941310133 := by
  rw [pow_two_pow_succ, u111]; decide
private theorem u113 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 113 =
      169074238445734738836133181821225245965387493 := by
  rw [pow_two_pow_succ, u112]; decide
private theorem u114 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 114 =
      443304886493902473458084464862662799421858405 := by
  rw [pow_two_pow_succ, u113]; decide
private theorem u115 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 115 =
      182050664268465887206387590014948503535493960 := by
  rw [pow_two_pow_succ, u114]; decide
private theorem u116 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 116 =
      427846460025470805092939482416440711892928368 := by
  rw [pow_two_pow_succ, u115]; decide
private theorem u117 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 117 =
      435780497342857953510376500039258474663499652 := by
  rw [pow_two_pow_succ, u116]; decide
private theorem u118 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 118 =
      79052560983842355002720243449006013870538947 := by
  rw [pow_two_pow_succ, u117]; decide
private theorem u119 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 119 =
      86663171033917087591494234253215281511320095 := by
  rw [pow_two_pow_succ, u118]; decide
private theorem u120 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 120 =
      94675662610877040350390253452549388500463508 := by
  rw [pow_two_pow_succ, u119]; decide
private theorem u121 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 121 =
      373310846659700514476671455481120006449897058 := by
  rw [pow_two_pow_succ, u120]; decide
private theorem u122 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 122 =
      333929667543507941265399272139577987063514142 := by
  rw [pow_two_pow_succ, u121]; decide
private theorem u123 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 123 =
      365776689002390431616511545157923604483360578 := by
  rw [pow_two_pow_succ, u122]; decide
private theorem u124 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 124 =
      283793094152882485959809308698918097646054052 := by
  rw [pow_two_pow_succ, u123]; decide
private theorem u125 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 125 =
      194804063170787753301841215952157073494575258 := by
  rw [pow_two_pow_succ, u124]; decide
private theorem u126 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 126 =
      403597799548417107293622254333834852706447187 := by
  rw [pow_two_pow_succ, u125]; decide
private theorem u127 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 127 =
      447431499464104329654112393943705681183899648 := by
  rw [pow_two_pow_succ, u126]; decide
private theorem u128 :
    (280171030852096594497184040840251869585814495 : ZMod P) ^ (2:ℕ) ^ 128 =
      1 := by
  rw [pow_two_pow_succ, u127]; decide

/-! ### The Lucas certificate -/

private theorem cert_main : (3 : ZMod P) ^ (P - 1) = 1 := by
  rw [show P - 1 = 1314883 * 2 ^ 128 from by norm_num, pow_mul, hx, u128]

private theorem cert_q2 : (3 : ZMod P) ^ ((P - 1) / 2) ≠ 1 := by
  rw [show (P - 1) / 2 = 1314883 * 2 ^ 127 from by norm_num, pow_mul, hx, u127]
  decide

private theorem cert_qh : (3 : ZMod P) ^ ((P - 1) / 1314883) ≠ 1 := by
  rw [show (P - 1) / 1314883 = 2 ^ 128 from by norm_num, t128]
  decide

/-- **`P` is prime** — Lucas certificate with witness `3`, cofactors `{2, 1314883}`. -/
theorem prime_P : Nat.Prime P := by
  refine lucas_primality P 3 cert_main ?_
  intro q hq hdvd
  rw [show P - 1 = 1314883 * 2 ^ 128 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · have hqh : q = 1314883 :=
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
    subst hqh
    exact cert_qh
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst hq2
    exact cert_q2

local instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩

/-! ### The order-32 element `g = 3^((P−1)/32) = u_123` -/

private theorem g_def :
    (3 : ZMod P) ^ ((P - 1) / 32) =
      365776689002390431616511545157923604483360578 := by
  rw [show (P - 1) / 32 = 1314883 * 2 ^ 123 from by norm_num, pow_mul, hx, u123]

/-- **The order-32 certificate.** -/
theorem orderOf_gP :
    orderOf (365776689002390431616511545157923604483360578 : ZMod P) = 32 := by
  have h4 : ¬ (365776689002390431616511545157923604483360578 : ZMod P) ^ (2:ℕ) ^ 4 = 1 := by
    decide
  have h8 : (365776689002390431616511545157923604483360578 : ZMod P) ^ (2:ℕ) ^ 5 = 1 := by
    decide
  have h := orderOf_eq_prime_pow
    (x := (365776689002390431616511545157923604483360578 : ZMod P)) h4 h8
  norm_num at h
  exact h

/-! ### The pin at the literal budget -/

private theorem choose_32_8 : (32 : ℕ).choose 8 = 10518300 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_16_8 : (16 : ℕ).choose 8 = 12870 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- **THE LITERAL-BUDGET PIN**: `δ* = 3/4` exactly at `ε* = 2⁻¹²⁸` for the dimension-7
(rate `7/32`) code on the 32-point smooth domain — the first exact in-window `δ*` at the
challenge's literal error budget.  Beyond Johnson (`8² = 64 < 224 = 7·32`). -/
theorem deltaStar_pin_literal_budget :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode
          (365776689002390431616511545157923604483360578 : ZMod P) 32 6)
        (1 / 2 ^ 128)
      = 3 / 4 := by
  haveI : NeZero (32 : ℕ) := ⟨by norm_num⟩
  have h := KKH26CeilingMarch.kkh26_march_deltaStar_pin (p := P) (μ := 5) (r := 8)
    (g := (365776689002390431616511545157923604483360578 : ZMod P)) (n := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact orderOf_gP) (by norm_num)
    (1 / 2 ^ 128) ?hlo ?hhi
  case hlo =>
    have hc : ((32 : ℕ).choose 8 / 8 : ℕ) = 1314787 := by rw [choose_32_8]
    rw [hc]
    exact band_lo_general (by norm_num) (by norm_num)
  case hhi =>
    have hc : (2 ^ 8 * (2 ^ (5 - 1)).choose 8 : ℕ) = 3294720 := by
      show (2 ^ 8 * (16 : ℕ).choose 8 : ℕ) = 3294720
      rw [choose_16_8]
      norm_num
    rw [hc]
    have hb := band_hi_general (e := 3294719) (q := P) (by norm_num)
    exact hb
  rw [h]
  have e2 : (((8 : ℕ)) : ℝ≥0) = (8 : ℝ≥0) := by norm_num
  rw [e2]
  have hd : (8 : ℝ≥0) / ((2 : ℝ≥0) ^ 5) = 8 / 32 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

end ArkLib.ProximityGap.LiteralBudgetPin

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.LiteralBudgetPin.prime_P
#print axioms ArkLib.ProximityGap.LiteralBudgetPin.orderOf_gP
#print axioms ArkLib.ProximityGap.LiteralBudgetPin.deltaStar_pin_literal_budget
