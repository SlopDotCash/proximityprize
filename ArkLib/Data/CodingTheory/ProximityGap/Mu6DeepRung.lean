/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SharpThresholdDischarge

/-!
# The deep rung: `δ* = 51/64` for the DIMENSION-12 code at `ε* = 2⁻¹²⁸` (#371)

The deepest member of the `n = 64` literal-budget family — the `r = 13` rung of
`Mu6LiteralBands.lean`, **unconditional** via the Landau sharpening: the dimension-12,
rate-`12/64 = 3/16` code (the closest-to-production rate of any unconditional in-window
pin to date), `δ* = 1 − 13/64 = 51/64`, beyond Johnson (`13² = 169 < 768 = 12·64`,
i.e. `1 − √(3/16) ≈ 0.567 < 51/64 ≈ 0.797 < 13/16` = capacity).

`P = 1010527601191·2¹²⁸ + 1 ≈ 2^{167.9}` (Proth; Lucas certificate, witness 3,
cofactors `{2, 1010527601191}`), inside the `r = 13` band
`[1010527600940·2¹²⁸, 2845684531200·2¹²⁸)`; the sharp threshold clears with huge margin
(`4³¹·128³² = 2²⁸⁶ < 2^{335.8} ≈ P²`).  Assembly: literal squaring chains →
`lucas_primality` → `orderOf_eq_prime_pow` → `not_dvd_collisionResultant_of_sq_lt` →
`kkh26_march_deltaStar_pin_of_not_dvd` + the `StaircaseBandTheorem` budget bridges.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 65536
set_option linter.constructorNameAsVariable false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ProximityGap.StaircaseBandTheorem

namespace ArkLib.ProximityGap.Mu6DeepRung

/-- The certified Proth prime `1010527601191·2^128 + 1 ≈ 2^167.9`. -/
abbrev P : ℕ := 343864723972211634234169339933846051930160125444097

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
      248335204424720420088016978550750770605348479314814 := by
  rw [pow_two_pow_succ, t6]; decide
private theorem t8 :
    (3 : ZMod P) ^ (2:ℕ) ^ 8 =
      163165008070857454044761320610398740020945171808263 := by
  rw [pow_two_pow_succ, t7]; decide
private theorem t9 :
    (3 : ZMod P) ^ (2:ℕ) ^ 9 =
      167805534469115480173941352720367376284966648741690 := by
  rw [pow_two_pow_succ, t8]; decide
private theorem t10 :
    (3 : ZMod P) ^ (2:ℕ) ^ 10 =
      298663313648263299947123945569632963297043199610180 := by
  rw [pow_two_pow_succ, t9]; decide
private theorem t11 :
    (3 : ZMod P) ^ (2:ℕ) ^ 11 =
      127714054127650993356046489038215936718120588159560 := by
  rw [pow_two_pow_succ, t10]; decide
private theorem t12 :
    (3 : ZMod P) ^ (2:ℕ) ^ 12 =
      310975491645719384388136731485087661543350010178165 := by
  rw [pow_two_pow_succ, t11]; decide
private theorem t13 :
    (3 : ZMod P) ^ (2:ℕ) ^ 13 =
      295626191195631097117363585254152402621465553988480 := by
  rw [pow_two_pow_succ, t12]; decide
private theorem t14 :
    (3 : ZMod P) ^ (2:ℕ) ^ 14 =
      240805619815462280207755877156038551321777938066292 := by
  rw [pow_two_pow_succ, t13]; decide
private theorem t15 :
    (3 : ZMod P) ^ (2:ℕ) ^ 15 =
      51433976265762340379340245448063413118563367262835 := by
  rw [pow_two_pow_succ, t14]; decide
private theorem t16 :
    (3 : ZMod P) ^ (2:ℕ) ^ 16 =
      113819669863919273776968229595654504090956888567682 := by
  rw [pow_two_pow_succ, t15]; decide
private theorem t17 :
    (3 : ZMod P) ^ (2:ℕ) ^ 17 =
      23007140257772428509849887341888734987896300355421 := by
  rw [pow_two_pow_succ, t16]; decide
private theorem t18 :
    (3 : ZMod P) ^ (2:ℕ) ^ 18 =
      256553392126546017203271427831250333971201343402327 := by
  rw [pow_two_pow_succ, t17]; decide
private theorem t19 :
    (3 : ZMod P) ^ (2:ℕ) ^ 19 =
      55895064178978253897197307910087550086968751129130 := by
  rw [pow_two_pow_succ, t18]; decide
private theorem t20 :
    (3 : ZMod P) ^ (2:ℕ) ^ 20 =
      266616962470995374911726740310655089437639585956290 := by
  rw [pow_two_pow_succ, t19]; decide
private theorem t21 :
    (3 : ZMod P) ^ (2:ℕ) ^ 21 =
      199318265866229694280244780112911878426716055200372 := by
  rw [pow_two_pow_succ, t20]; decide
private theorem t22 :
    (3 : ZMod P) ^ (2:ℕ) ^ 22 =
      280268710597160245761448841247204350361609859930289 := by
  rw [pow_two_pow_succ, t21]; decide
private theorem t23 :
    (3 : ZMod P) ^ (2:ℕ) ^ 23 =
      35706077101625963348431813515101939813141073192261 := by
  rw [pow_two_pow_succ, t22]; decide
private theorem t24 :
    (3 : ZMod P) ^ (2:ℕ) ^ 24 =
      4738607660211316648617558860949353333587155171939 := by
  rw [pow_two_pow_succ, t23]; decide
private theorem t25 :
    (3 : ZMod P) ^ (2:ℕ) ^ 25 =
      267508037130491050645054348539244834884755885656218 := by
  rw [pow_two_pow_succ, t24]; decide
private theorem t26 :
    (3 : ZMod P) ^ (2:ℕ) ^ 26 =
      88134645127725534387889189168986320325055335628498 := by
  rw [pow_two_pow_succ, t25]; decide
private theorem t27 :
    (3 : ZMod P) ^ (2:ℕ) ^ 27 =
      124483281483437226149371059947106196307611701096255 := by
  rw [pow_two_pow_succ, t26]; decide
private theorem t28 :
    (3 : ZMod P) ^ (2:ℕ) ^ 28 =
      91099885562952655231249044085657512580347715085311 := by
  rw [pow_two_pow_succ, t27]; decide
private theorem t29 :
    (3 : ZMod P) ^ (2:ℕ) ^ 29 =
      271387253403185646041608883153981304345367966740284 := by
  rw [pow_two_pow_succ, t28]; decide
private theorem t30 :
    (3 : ZMod P) ^ (2:ℕ) ^ 30 =
      250176890063204925603172938649733800530876525638569 := by
  rw [pow_two_pow_succ, t29]; decide
private theorem t31 :
    (3 : ZMod P) ^ (2:ℕ) ^ 31 =
      140259504100540946960950971943786795721349971235899 := by
  rw [pow_two_pow_succ, t30]; decide
private theorem t32 :
    (3 : ZMod P) ^ (2:ℕ) ^ 32 =
      336259967320469601992854181366023301270284106941875 := by
  rw [pow_two_pow_succ, t31]; decide
private theorem t33 :
    (3 : ZMod P) ^ (2:ℕ) ^ 33 =
      67095435938295293548123213950757537318791862855367 := by
  rw [pow_two_pow_succ, t32]; decide
private theorem t34 :
    (3 : ZMod P) ^ (2:ℕ) ^ 34 =
      192628674667514489600873563038528862823499240348289 := by
  rw [pow_two_pow_succ, t33]; decide
private theorem t35 :
    (3 : ZMod P) ^ (2:ℕ) ^ 35 =
      317888900849439711754379068947634252561911398911780 := by
  rw [pow_two_pow_succ, t34]; decide
private theorem t36 :
    (3 : ZMod P) ^ (2:ℕ) ^ 36 =
      34001525125778546865407894483859263253520787609945 := by
  rw [pow_two_pow_succ, t35]; decide
private theorem t37 :
    (3 : ZMod P) ^ (2:ℕ) ^ 37 =
      142286730605678884378223519202761508164353302560693 := by
  rw [pow_two_pow_succ, t36]; decide
private theorem t38 :
    (3 : ZMod P) ^ (2:ℕ) ^ 38 =
      159731056591798436847076060931763113549781620153020 := by
  rw [pow_two_pow_succ, t37]; decide
private theorem t39 :
    (3 : ZMod P) ^ (2:ℕ) ^ 39 =
      228091161200035250308472298488768326803656908764435 := by
  rw [pow_two_pow_succ, t38]; decide
private theorem t40 :
    (3 : ZMod P) ^ (2:ℕ) ^ 40 =
      275593589122692028727966471180964969034983985357841 := by
  rw [pow_two_pow_succ, t39]; decide
private theorem t41 :
    (3 : ZMod P) ^ (2:ℕ) ^ 41 =
      331747315951307267216944975589552117539616399712777 := by
  rw [pow_two_pow_succ, t40]; decide
private theorem t42 :
    (3 : ZMod P) ^ (2:ℕ) ^ 42 =
      327401864600680502104733817763024914051825998293782 := by
  rw [pow_two_pow_succ, t41]; decide
private theorem t43 :
    (3 : ZMod P) ^ (2:ℕ) ^ 43 =
      64431512014017854115463218661714612291043405289171 := by
  rw [pow_two_pow_succ, t42]; decide
private theorem t44 :
    (3 : ZMod P) ^ (2:ℕ) ^ 44 =
      98865359989354990313908383567375301238676224067563 := by
  rw [pow_two_pow_succ, t43]; decide
private theorem t45 :
    (3 : ZMod P) ^ (2:ℕ) ^ 45 =
      136176424757288776057864021135838485978135044343295 := by
  rw [pow_two_pow_succ, t44]; decide
private theorem t46 :
    (3 : ZMod P) ^ (2:ℕ) ^ 46 =
      112438840432859367538991389398985227671218217559242 := by
  rw [pow_two_pow_succ, t45]; decide
private theorem t47 :
    (3 : ZMod P) ^ (2:ℕ) ^ 47 =
      277576865939918892189091625723689442431095180130132 := by
  rw [pow_two_pow_succ, t46]; decide
private theorem t48 :
    (3 : ZMod P) ^ (2:ℕ) ^ 48 =
      228139611197106754648019500116792271325049349524567 := by
  rw [pow_two_pow_succ, t47]; decide
private theorem t49 :
    (3 : ZMod P) ^ (2:ℕ) ^ 49 =
      131528105457056147151167899269824704863140966528989 := by
  rw [pow_two_pow_succ, t48]; decide
private theorem t50 :
    (3 : ZMod P) ^ (2:ℕ) ^ 50 =
      304121373322627989862350018771358476003540309270486 := by
  rw [pow_two_pow_succ, t49]; decide
private theorem t51 :
    (3 : ZMod P) ^ (2:ℕ) ^ 51 =
      117263629256174653498928743513687031524002065917392 := by
  rw [pow_two_pow_succ, t50]; decide
private theorem t52 :
    (3 : ZMod P) ^ (2:ℕ) ^ 52 =
      232474345459279711425376069749601584449600712765488 := by
  rw [pow_two_pow_succ, t51]; decide
private theorem t53 :
    (3 : ZMod P) ^ (2:ℕ) ^ 53 =
      311584975735108613365966533307567609335780562141394 := by
  rw [pow_two_pow_succ, t52]; decide
private theorem t54 :
    (3 : ZMod P) ^ (2:ℕ) ^ 54 =
      266028021498900673290833308145587418098654530816972 := by
  rw [pow_two_pow_succ, t53]; decide
private theorem t55 :
    (3 : ZMod P) ^ (2:ℕ) ^ 55 =
      6554469750160338228307652936771099199976134336743 := by
  rw [pow_two_pow_succ, t54]; decide
private theorem t56 :
    (3 : ZMod P) ^ (2:ℕ) ^ 56 =
      155701793635385363631188998057220594666954213126275 := by
  rw [pow_two_pow_succ, t55]; decide
private theorem t57 :
    (3 : ZMod P) ^ (2:ℕ) ^ 57 =
      177167597140237489039974519249514499488624672882544 := by
  rw [pow_two_pow_succ, t56]; decide
private theorem t58 :
    (3 : ZMod P) ^ (2:ℕ) ^ 58 =
      185211570457032355677343469003472875584863549685786 := by
  rw [pow_two_pow_succ, t57]; decide
private theorem t59 :
    (3 : ZMod P) ^ (2:ℕ) ^ 59 =
      166687459136945836603697093795799609153887977067696 := by
  rw [pow_two_pow_succ, t58]; decide
private theorem t60 :
    (3 : ZMod P) ^ (2:ℕ) ^ 60 =
      30604288545512956439802310387266857118927591427205 := by
  rw [pow_two_pow_succ, t59]; decide
private theorem t61 :
    (3 : ZMod P) ^ (2:ℕ) ^ 61 =
      274002141576089038376272512443198155685927018694431 := by
  rw [pow_two_pow_succ, t60]; decide
private theorem t62 :
    (3 : ZMod P) ^ (2:ℕ) ^ 62 =
      335889319264966208197803629549250983457773810276305 := by
  rw [pow_two_pow_succ, t61]; decide
private theorem t63 :
    (3 : ZMod P) ^ (2:ℕ) ^ 63 =
      228281587042175941611830985906193469448785669355063 := by
  rw [pow_two_pow_succ, t62]; decide
private theorem t64 :
    (3 : ZMod P) ^ (2:ℕ) ^ 64 =
      47542486048036595753139555107287637983667244370992 := by
  rw [pow_two_pow_succ, t63]; decide
private theorem t65 :
    (3 : ZMod P) ^ (2:ℕ) ^ 65 =
      225153686816965429694670830947416249113220571614448 := by
  rw [pow_two_pow_succ, t64]; decide
private theorem t66 :
    (3 : ZMod P) ^ (2:ℕ) ^ 66 =
      122881584200077438555601274271236859866593212249938 := by
  rw [pow_two_pow_succ, t65]; decide
private theorem t67 :
    (3 : ZMod P) ^ (2:ℕ) ^ 67 =
      51669293818850668438662052048089845764373786663165 := by
  rw [pow_two_pow_succ, t66]; decide
private theorem t68 :
    (3 : ZMod P) ^ (2:ℕ) ^ 68 =
      72793837261328079289742228343196701902751086580148 := by
  rw [pow_two_pow_succ, t67]; decide
private theorem t69 :
    (3 : ZMod P) ^ (2:ℕ) ^ 69 =
      122063033190849896251882698246011777503470488703225 := by
  rw [pow_two_pow_succ, t68]; decide
private theorem t70 :
    (3 : ZMod P) ^ (2:ℕ) ^ 70 =
      71796878597860379818001960817485207971586087453785 := by
  rw [pow_two_pow_succ, t69]; decide
private theorem t71 :
    (3 : ZMod P) ^ (2:ℕ) ^ 71 =
      317823640949906838952888361776645796946058656664686 := by
  rw [pow_two_pow_succ, t70]; decide
private theorem t72 :
    (3 : ZMod P) ^ (2:ℕ) ^ 72 =
      50456169803341439517090854430668726239957645631188 := by
  rw [pow_two_pow_succ, t71]; decide
private theorem t73 :
    (3 : ZMod P) ^ (2:ℕ) ^ 73 =
      213807776042741463131411950187653408698630279297732 := by
  rw [pow_two_pow_succ, t72]; decide
private theorem t74 :
    (3 : ZMod P) ^ (2:ℕ) ^ 74 =
      340965088722204601716485726581588646324380236393272 := by
  rw [pow_two_pow_succ, t73]; decide
private theorem t75 :
    (3 : ZMod P) ^ (2:ℕ) ^ 75 =
      301121115706878244542625304350940461329605437034849 := by
  rw [pow_two_pow_succ, t74]; decide
private theorem t76 :
    (3 : ZMod P) ^ (2:ℕ) ^ 76 =
      289578803611799730953423654665985375962165192495400 := by
  rw [pow_two_pow_succ, t75]; decide
private theorem t77 :
    (3 : ZMod P) ^ (2:ℕ) ^ 77 =
      54756756961146825014376162004253342921330432247639 := by
  rw [pow_two_pow_succ, t76]; decide
private theorem t78 :
    (3 : ZMod P) ^ (2:ℕ) ^ 78 =
      292783269563600573427537997803029992409443235125680 := by
  rw [pow_two_pow_succ, t77]; decide
private theorem t79 :
    (3 : ZMod P) ^ (2:ℕ) ^ 79 =
      174237372835217145060465513029682656556054002042733 := by
  rw [pow_two_pow_succ, t78]; decide
private theorem t80 :
    (3 : ZMod P) ^ (2:ℕ) ^ 80 =
      230572096648214410305717698915287936714105638819765 := by
  rw [pow_two_pow_succ, t79]; decide
private theorem t81 :
    (3 : ZMod P) ^ (2:ℕ) ^ 81 =
      229958676471329849673243762558649664068910889549953 := by
  rw [pow_two_pow_succ, t80]; decide
private theorem t82 :
    (3 : ZMod P) ^ (2:ℕ) ^ 82 =
      52842369596398090055802420295074851384025234556615 := by
  rw [pow_two_pow_succ, t81]; decide
private theorem t83 :
    (3 : ZMod P) ^ (2:ℕ) ^ 83 =
      287781673773552554270737861143786006542431017452061 := by
  rw [pow_two_pow_succ, t82]; decide
private theorem t84 :
    (3 : ZMod P) ^ (2:ℕ) ^ 84 =
      104540011335561103907524671387493914970466377787438 := by
  rw [pow_two_pow_succ, t83]; decide
private theorem t85 :
    (3 : ZMod P) ^ (2:ℕ) ^ 85 =
      325872042765449219031634449557764751027563553700982 := by
  rw [pow_two_pow_succ, t84]; decide
private theorem t86 :
    (3 : ZMod P) ^ (2:ℕ) ^ 86 =
      201565760682984523805352605485784029795050364618657 := by
  rw [pow_two_pow_succ, t85]; decide
private theorem t87 :
    (3 : ZMod P) ^ (2:ℕ) ^ 87 =
      80475232168706989581784837998617898288021725113225 := by
  rw [pow_two_pow_succ, t86]; decide
private theorem t88 :
    (3 : ZMod P) ^ (2:ℕ) ^ 88 =
      276662387803385562352468801452430950685021514043932 := by
  rw [pow_two_pow_succ, t87]; decide
private theorem t89 :
    (3 : ZMod P) ^ (2:ℕ) ^ 89 =
      332595451396916990333707766559280491987669809106886 := by
  rw [pow_two_pow_succ, t88]; decide
private theorem t90 :
    (3 : ZMod P) ^ (2:ℕ) ^ 90 =
      232881057949640598911495442656272961782792832582952 := by
  rw [pow_two_pow_succ, t89]; decide
private theorem t91 :
    (3 : ZMod P) ^ (2:ℕ) ^ 91 =
      311612553598395505649639431266612237478471108875293 := by
  rw [pow_two_pow_succ, t90]; decide
private theorem t92 :
    (3 : ZMod P) ^ (2:ℕ) ^ 92 =
      33000468852299973341224594991091715547548064807685 := by
  rw [pow_two_pow_succ, t91]; decide
private theorem t93 :
    (3 : ZMod P) ^ (2:ℕ) ^ 93 =
      124789711405222019321903422556947735466494570410810 := by
  rw [pow_two_pow_succ, t92]; decide
private theorem t94 :
    (3 : ZMod P) ^ (2:ℕ) ^ 94 =
      307667055481302450417611187056239571530530332204586 := by
  rw [pow_two_pow_succ, t93]; decide
private theorem t95 :
    (3 : ZMod P) ^ (2:ℕ) ^ 95 =
      313324227892588492843354566914567388098238060181467 := by
  rw [pow_two_pow_succ, t94]; decide
private theorem t96 :
    (3 : ZMod P) ^ (2:ℕ) ^ 96 =
      193595476592240230242009994470401464570497867734587 := by
  rw [pow_two_pow_succ, t95]; decide
private theorem t97 :
    (3 : ZMod P) ^ (2:ℕ) ^ 97 =
      136355183283258721601368874636178009715280070541655 := by
  rw [pow_two_pow_succ, t96]; decide
private theorem t98 :
    (3 : ZMod P) ^ (2:ℕ) ^ 98 =
      135210894460022550332442519356208815916936446279356 := by
  rw [pow_two_pow_succ, t97]; decide
private theorem t99 :
    (3 : ZMod P) ^ (2:ℕ) ^ 99 =
      189506004707881982702718248011482114509198599752677 := by
  rw [pow_two_pow_succ, t98]; decide
private theorem t100 :
    (3 : ZMod P) ^ (2:ℕ) ^ 100 =
      300277880508234520129523339094302860647011022376551 := by
  rw [pow_two_pow_succ, t99]; decide
private theorem t101 :
    (3 : ZMod P) ^ (2:ℕ) ^ 101 =
      32057538504810205410761774669670569928223257174234 := by
  rw [pow_two_pow_succ, t100]; decide
private theorem t102 :
    (3 : ZMod P) ^ (2:ℕ) ^ 102 =
      16289874328218092379311089373301235906506589420560 := by
  rw [pow_two_pow_succ, t101]; decide
private theorem t103 :
    (3 : ZMod P) ^ (2:ℕ) ^ 103 =
      27793063640778535437144082724366262201843126115355 := by
  rw [pow_two_pow_succ, t102]; decide
private theorem t104 :
    (3 : ZMod P) ^ (2:ℕ) ^ 104 =
      82559532557640617454074901358901238437299659703895 := by
  rw [pow_two_pow_succ, t103]; decide
private theorem t105 :
    (3 : ZMod P) ^ (2:ℕ) ^ 105 =
      188423060443490007255010394855706280080152146968423 := by
  rw [pow_two_pow_succ, t104]; decide
private theorem t106 :
    (3 : ZMod P) ^ (2:ℕ) ^ 106 =
      187553959214635929087323542863539876643300495878008 := by
  rw [pow_two_pow_succ, t105]; decide
private theorem t107 :
    (3 : ZMod P) ^ (2:ℕ) ^ 107 =
      139179655190869234994331974669574501952537682103991 := by
  rw [pow_two_pow_succ, t106]; decide
private theorem t108 :
    (3 : ZMod P) ^ (2:ℕ) ^ 108 =
      230237686507067869218689855643142395066604510707304 := by
  rw [pow_two_pow_succ, t107]; decide
private theorem t109 :
    (3 : ZMod P) ^ (2:ℕ) ^ 109 =
      206009280734432442649190417990124958188479778797527 := by
  rw [pow_two_pow_succ, t108]; decide
private theorem t110 :
    (3 : ZMod P) ^ (2:ℕ) ^ 110 =
      124538801952748638702222224597439085094255206668422 := by
  rw [pow_two_pow_succ, t109]; decide
private theorem t111 :
    (3 : ZMod P) ^ (2:ℕ) ^ 111 =
      195506921372868579147992777687702489763111807672591 := by
  rw [pow_two_pow_succ, t110]; decide
private theorem t112 :
    (3 : ZMod P) ^ (2:ℕ) ^ 112 =
      77887881491604176754565886282088502720605948561774 := by
  rw [pow_two_pow_succ, t111]; decide
private theorem t113 :
    (3 : ZMod P) ^ (2:ℕ) ^ 113 =
      320413702013207658066542363312118174250630260200944 := by
  rw [pow_two_pow_succ, t112]; decide
private theorem t114 :
    (3 : ZMod P) ^ (2:ℕ) ^ 114 =
      60969904731484674384720782808641935156865197443231 := by
  rw [pow_two_pow_succ, t113]; decide
private theorem t115 :
    (3 : ZMod P) ^ (2:ℕ) ^ 115 =
      225800276399144070092731725612095583820209518209018 := by
  rw [pow_two_pow_succ, t114]; decide
private theorem t116 :
    (3 : ZMod P) ^ (2:ℕ) ^ 116 =
      21027313423170323450638094538788558921712515594505 := by
  rw [pow_two_pow_succ, t115]; decide
private theorem t117 :
    (3 : ZMod P) ^ (2:ℕ) ^ 117 =
      191629579677929754100653384533097157031647088515370 := by
  rw [pow_two_pow_succ, t116]; decide
private theorem t118 :
    (3 : ZMod P) ^ (2:ℕ) ^ 118 =
      289646083786892946167128842478843736188497227850604 := by
  rw [pow_two_pow_succ, t117]; decide
private theorem t119 :
    (3 : ZMod P) ^ (2:ℕ) ^ 119 =
      250634971522697800414730587982681331576483211362174 := by
  rw [pow_two_pow_succ, t118]; decide
private theorem t120 :
    (3 : ZMod P) ^ (2:ℕ) ^ 120 =
      286168577548331489032841454440474636482827346743388 := by
  rw [pow_two_pow_succ, t119]; decide
private theorem t121 :
    (3 : ZMod P) ^ (2:ℕ) ^ 121 =
      48221550157171219942439574193146139886984307549238 := by
  rw [pow_two_pow_succ, t120]; decide
private theorem t122 :
    (3 : ZMod P) ^ (2:ℕ) ^ 122 =
      180610131113031086195921292266552565018048452397465 := by
  rw [pow_two_pow_succ, t121]; decide
private theorem t123 :
    (3 : ZMod P) ^ (2:ℕ) ^ 123 =
      83214830794798064062591600599451377837193573604443 := by
  rw [pow_two_pow_succ, t122]; decide
private theorem t124 :
    (3 : ZMod P) ^ (2:ℕ) ^ 124 =
      73069860881527932750195650434456862130248263778742 := by
  rw [pow_two_pow_succ, t123]; decide
private theorem t125 :
    (3 : ZMod P) ^ (2:ℕ) ^ 125 =
      14235541189234794254986407701840324248737006998168 := by
  rw [pow_two_pow_succ, t124]; decide
private theorem t126 :
    (3 : ZMod P) ^ (2:ℕ) ^ 126 =
      298092129275702723431226084718692208247310272243932 := by
  rw [pow_two_pow_succ, t125]; decide
private theorem t127 :
    (3 : ZMod P) ^ (2:ℕ) ^ 127 =
      245438217892419288433479158757446601146348248690960 := by
  rw [pow_two_pow_succ, t126]; decide
private theorem t128 :
    (3 : ZMod P) ^ (2:ℕ) ^ 128 =
      285558015145463997081870925367629524681904351756877 := by
  rw [pow_two_pow_succ, t127]; decide

private theorem hx :
    (3 : ZMod P) ^ (1010527601191:ℕ) =
      286927782233639517182935977911655064918370995773952 := by
  rw [show (1010527601191:ℕ)
      = 2^39 + 2^38 + 2^37 + 2^35 + 2^33 + 2^32 + 2^30 + 2^27 + 2^21
        + 2^17 + 2^16 + 2^15 + 2^9 + 2^5 + 2^2 + 2^1 + 2^0
      from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    t39, t38, t37, t35, t33, t32, t30, t27, t21, t17, t16, t15, t9, t5, t2, t1, t0]
  decide

private theorem u0 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 0 =
      286927782233639517182935977911655064918370995773952 := by
  norm_num
private theorem u1 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 1 =
      129151795139060385301717464224076673484459263474527 := by
  rw [pow_two_pow_succ, u0]; decide
private theorem u2 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 2 =
      153923426882701584305080653478816342279302925581890 := by
  rw [pow_two_pow_succ, u1]; decide
private theorem u3 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 3 =
      77894849233737995496918195239468065937544232660739 := by
  rw [pow_two_pow_succ, u2]; decide
private theorem u4 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 4 =
      229105621669168353275494013283107180405535393055594 := by
  rw [pow_two_pow_succ, u3]; decide
private theorem u5 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 5 =
      177029852281706009720270800369700857748050094361816 := by
  rw [pow_two_pow_succ, u4]; decide
private theorem u6 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 6 =
      153043270031150795560847831527811711080274260459592 := by
  rw [pow_two_pow_succ, u5]; decide
private theorem u7 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 7 =
      182739232696271566667934336632232047667925536851735 := by
  rw [pow_two_pow_succ, u6]; decide
private theorem u8 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 8 =
      134480578345074959849217508350091714968281723031625 := by
  rw [pow_two_pow_succ, u7]; decide
private theorem u9 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 9 =
      103946315664518047173128532007701101065315634786998 := by
  rw [pow_two_pow_succ, u8]; decide
private theorem u10 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 10 =
      86853878489361664796425229809626323179858646333493 := by
  rw [pow_two_pow_succ, u9]; decide
private theorem u11 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 11 =
      233388929784596778759502419562273716175273051156008 := by
  rw [pow_two_pow_succ, u10]; decide
private theorem u12 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 12 =
      323746539256269359554973393412808372190757104620621 := by
  rw [pow_two_pow_succ, u11]; decide
private theorem u13 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 13 =
      127952718940249964598956542210002304865259485742967 := by
  rw [pow_two_pow_succ, u12]; decide
private theorem u14 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 14 =
      148328960758454035523868377161114017186255592282753 := by
  rw [pow_two_pow_succ, u13]; decide
private theorem u15 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 15 =
      119089644379540095186486821707304595510029002209061 := by
  rw [pow_two_pow_succ, u14]; decide
private theorem u16 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 16 =
      232021057056049581436712289779250135547984326655846 := by
  rw [pow_two_pow_succ, u15]; decide
private theorem u17 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 17 =
      319826609146491822800531557623274366875191354161499 := by
  rw [pow_two_pow_succ, u16]; decide
private theorem u18 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 18 =
      202221511130787555627488620100124031545381270935938 := by
  rw [pow_two_pow_succ, u17]; decide
private theorem u19 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 19 =
      130778285721885919694145675480894135770313590845600 := by
  rw [pow_two_pow_succ, u18]; decide
private theorem u20 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 20 =
      127650248304605426447947731750968586163210928922417 := by
  rw [pow_two_pow_succ, u19]; decide
private theorem u21 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 21 =
      241826582198578650342811713833784622000972684179046 := by
  rw [pow_two_pow_succ, u20]; decide
private theorem u22 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 22 =
      253147812267748837054183115551991291821104387173116 := by
  rw [pow_two_pow_succ, u21]; decide
private theorem u23 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 23 =
      5163312451579161409650343598980306780043864664463 := by
  rw [pow_two_pow_succ, u22]; decide
private theorem u24 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 24 =
      214238437888852028660064200937089826136938145770488 := by
  rw [pow_two_pow_succ, u23]; decide
private theorem u25 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 25 =
      73409787350402394639993924194754742748856110648990 := by
  rw [pow_two_pow_succ, u24]; decide
private theorem u26 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 26 =
      85290133095784355547576995679065301257322314258824 := by
  rw [pow_two_pow_succ, u25]; decide
private theorem u27 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 27 =
      311075594549361890024644099192666218947541790832757 := by
  rw [pow_two_pow_succ, u26]; decide
private theorem u28 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 28 =
      281559707965658458810409227046466752260142459940352 := by
  rw [pow_two_pow_succ, u27]; decide
private theorem u29 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 29 =
      116544363873074011008777057403377323633565648117851 := by
  rw [pow_two_pow_succ, u28]; decide
private theorem u30 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 30 =
      138443775246630166819399563015628364457142712361508 := by
  rw [pow_two_pow_succ, u29]; decide
private theorem u31 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 31 =
      313859324494257764227485572341398371882444758222607 := by
  rw [pow_two_pow_succ, u30]; decide
private theorem u32 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 32 =
      131218956332431520303319499338519191852230180054130 := by
  rw [pow_two_pow_succ, u31]; decide
private theorem u33 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 33 =
      206216851351090391852743319059595801151883610373721 := by
  rw [pow_two_pow_succ, u32]; decide
private theorem u34 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 34 =
      165508879949731664038102830815730187825965828910757 := by
  rw [pow_two_pow_succ, u33]; decide
private theorem u35 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 35 =
      27759218464843072356074373417751294076851619669442 := by
  rw [pow_two_pow_succ, u34]; decide
private theorem u36 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 36 =
      297957200864575712294861922593075635783845176014222 := by
  rw [pow_two_pow_succ, u35]; decide
private theorem u37 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 37 =
      102109642644276672529367106418110908723578960410605 := by
  rw [pow_two_pow_succ, u36]; decide
private theorem u38 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 38 =
      136298844684444533983479397379287591291059830974857 := by
  rw [pow_two_pow_succ, u37]; decide
private theorem u39 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 39 =
      40187059035120344399574201869320329413411586931318 := by
  rw [pow_two_pow_succ, u38]; decide
private theorem u40 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 40 =
      83962727667046893373213531333561841294734708933268 := by
  rw [pow_two_pow_succ, u39]; decide
private theorem u41 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 41 =
      238954334713802060455212125810708592419253924266764 := by
  rw [pow_two_pow_succ, u40]; decide
private theorem u42 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 42 =
      65522765071429377919766238077132601827530126993568 := by
  rw [pow_two_pow_succ, u41]; decide
private theorem u43 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 43 =
      329091518662407717323516254342448109343081368772365 := by
  rw [pow_two_pow_succ, u42]; decide
private theorem u44 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 44 =
      49649276673931495696258032871794328104969294927423 := by
  rw [pow_two_pow_succ, u43]; decide
private theorem u45 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 45 =
      163766443272123217966352006795822969548877532011400 := by
  rw [pow_two_pow_succ, u44]; decide
private theorem u46 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 46 =
      185531817174679689549505703036272290883489186071489 := by
  rw [pow_two_pow_succ, u45]; decide
private theorem u47 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 47 =
      162919931727830590393122948586162618143523966652663 := by
  rw [pow_two_pow_succ, u46]; decide
private theorem u48 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 48 =
      106507735795418148742953183854083191865301251114315 := by
  rw [pow_two_pow_succ, u47]; decide
private theorem u49 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 49 =
      91793574560193294467991968325720264571386776815491 := by
  rw [pow_two_pow_succ, u48]; decide
private theorem u50 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 50 =
      119864863722938758046477344121637739618817280916361 := by
  rw [pow_two_pow_succ, u49]; decide
private theorem u51 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 51 =
      273795479514380859480794842209911588823415411457006 := by
  rw [pow_two_pow_succ, u50]; decide
private theorem u52 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 52 =
      56733129187555977399210095649419043870329950403914 := by
  rw [pow_two_pow_succ, u51]; decide
private theorem u53 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 53 =
      153640554304552980743316915183472051017092741006395 := by
  rw [pow_two_pow_succ, u52]; decide
private theorem u54 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 54 =
      280024559985640383964827312482643484248115226020946 := by
  rw [pow_two_pow_succ, u53]; decide
private theorem u55 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 55 =
      226036589390995715232195683334465840005955396949383 := by
  rw [pow_two_pow_succ, u54]; decide
private theorem u56 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 56 =
      126987214293304990949900823569831971448090887716632 := by
  rw [pow_two_pow_succ, u55]; decide
private theorem u57 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 57 =
      258808969337416220605405855587355831542953576189987 := by
  rw [pow_two_pow_succ, u56]; decide
private theorem u58 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 58 =
      220718599638070533242215989087319544683045989147348 := by
  rw [pow_two_pow_succ, u57]; decide
private theorem u59 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 59 =
      44032680038129375001460366577824960044263447535464 := by
  rw [pow_two_pow_succ, u58]; decide
private theorem u60 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 60 =
      7710288099929494397350784602928408356122401950302 := by
  rw [pow_two_pow_succ, u59]; decide
private theorem u61 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 61 =
      275994062763143247861815022001590295843345877352428 := by
  rw [pow_two_pow_succ, u60]; decide
private theorem u62 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 62 =
      87498598531964178211201795374988515115627189246346 := by
  rw [pow_two_pow_succ, u61]; decide
private theorem u63 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 63 =
      198688894612792978934015128345173188341587364405981 := by
  rw [pow_two_pow_succ, u62]; decide
private theorem u64 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 64 =
      68216692611382264551505470694495654516592217711309 := by
  rw [pow_two_pow_succ, u63]; decide
private theorem u65 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 65 =
      290820678246432037036173061332919234555443596301930 := by
  rw [pow_two_pow_succ, u64]; decide
private theorem u66 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 66 =
      32188227877103035238638723202297831198286306742507 := by
  rw [pow_two_pow_succ, u65]; decide
private theorem u67 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 67 =
      339751301940337301740690741125910759329796572547568 := by
  rw [pow_two_pow_succ, u66]; decide
private theorem u68 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 68 =
      83638461278453228755241538235057828188398526774236 := by
  rw [pow_two_pow_succ, u67]; decide
private theorem u69 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 69 =
      254584389798270836733117297547676347221373888853279 := by
  rw [pow_two_pow_succ, u68]; decide
private theorem u70 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 70 =
      126677915028390416723711150720858025768932941403228 := by
  rw [pow_two_pow_succ, u69]; decide
private theorem u71 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 71 =
      214663803879133058971937473517910391698463025113066 := by
  rw [pow_two_pow_succ, u70]; decide
private theorem u72 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 72 =
      203671959899589051178457262444670043387150429268317 := by
  rw [pow_two_pow_succ, u71]; decide
private theorem u73 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 73 =
      2656462087097080852408155056164366429719929725292 := by
  rw [pow_two_pow_succ, u72]; decide
private theorem u74 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 74 =
      309368075852175054226118964470931436584972102949134 := by
  rw [pow_two_pow_succ, u73]; decide
private theorem u75 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 75 =
      200350266494418322134217298605204553089783143739091 := by
  rw [pow_two_pow_succ, u74]; decide
private theorem u76 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 76 =
      143303745913969239108213933646651499273161264326223 := by
  rw [pow_two_pow_succ, u75]; decide
private theorem u77 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 77 =
      271068508306696691685320555363501556220379686859288 := by
  rw [pow_two_pow_succ, u76]; decide
private theorem u78 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 78 =
      317513120531578078030070875041767236207343990152400 := by
  rw [pow_two_pow_succ, u77]; decide
private theorem u79 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 79 =
      118024876384831365693693686616145664339524796272688 := by
  rw [pow_two_pow_succ, u78]; decide
private theorem u80 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 80 =
      295058521325413422845621940357075639177230868542741 := by
  rw [pow_two_pow_succ, u79]; decide
private theorem u81 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 81 =
      37683426010160517447623415812869641151023778498216 := by
  rw [pow_two_pow_succ, u80]; decide
private theorem u82 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 82 =
      229050658233744547980925847546221677269381789482424 := by
  rw [pow_two_pow_succ, u81]; decide
private theorem u83 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 83 =
      230536536920839572701791968054048511666023016445779 := by
  rw [pow_two_pow_succ, u82]; decide
private theorem u84 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 84 =
      18463546501233498988376450268035273871009348481937 := by
  rw [pow_two_pow_succ, u83]; decide
private theorem u85 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 85 =
      291773497712399276343990665954179506036111610374406 := by
  rw [pow_two_pow_succ, u84]; decide
private theorem u86 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 86 =
      272090410599940228580151568733123138950317868629553 := by
  rw [pow_two_pow_succ, u85]; decide
private theorem u87 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 87 =
      75382605099056990912334241414852916198038908138188 := by
  rw [pow_two_pow_succ, u86]; decide
private theorem u88 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 88 =
      258879231304649705968085546200659817471325194027090 := by
  rw [pow_two_pow_succ, u87]; decide
private theorem u89 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 89 =
      20227418319849526088605388799925166190213931621149 := by
  rw [pow_two_pow_succ, u88]; decide
private theorem u90 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 90 =
      14494140665029040121448365271679296815768579499071 := by
  rw [pow_two_pow_succ, u89]; decide
private theorem u91 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 91 =
      224828801746713179066885424951146046580369778359384 := by
  rw [pow_two_pow_succ, u90]; decide
private theorem u92 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 92 =
      322827820950949497541541935534306933212984801011238 := by
  rw [pow_two_pow_succ, u91]; decide
private theorem u93 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 93 =
      76147865148975122543734545716256586310151678148879 := by
  rw [pow_two_pow_succ, u92]; decide
private theorem u94 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 94 =
      275065549564932397038519479975344593092180919641862 := by
  rw [pow_two_pow_succ, u93]; decide
private theorem u95 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 95 =
      5088343983505381459913844541481039530243725217859 := by
  rw [pow_two_pow_succ, u94]; decide
private theorem u96 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 96 =
      235720697130766815662606008767305933552896581128318 := by
  rw [pow_two_pow_succ, u95]; decide
private theorem u97 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 97 =
      103407829674878834832972838547940071588834513295139 := by
  rw [pow_two_pow_succ, u96]; decide
private theorem u98 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 98 =
      163933341733231027010766688755501873580158540089949 := by
  rw [pow_two_pow_succ, u97]; decide
private theorem u99 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 99 =
      258167030058043413413181673239226446134441624124888 := by
  rw [pow_two_pow_succ, u98]; decide
private theorem u100 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 100 =
      8207618636394962751283040988462788166506861183982 := by
  rw [pow_two_pow_succ, u99]; decide
private theorem u101 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 101 =
      291211627363209386762101284938613891844598656271345 := by
  rw [pow_two_pow_succ, u100]; decide
private theorem u102 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 102 =
      163169188509684070249003541221792626463578969077563 := by
  rw [pow_two_pow_succ, u101]; decide
private theorem u103 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 103 =
      37501765272365803200596642929408627807093448341296 := by
  rw [pow_two_pow_succ, u102]; decide
private theorem u104 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 104 =
      95732769229109475170002984687715354983621545519622 := by
  rw [pow_two_pow_succ, u103]; decide
private theorem u105 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 105 =
      185386055486658226351720618215340449571528756330080 := by
  rw [pow_two_pow_succ, u104]; decide
private theorem u106 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 106 =
      101956617666024051165890846519122238700506027258736 := by
  rw [pow_two_pow_succ, u105]; decide
private theorem u107 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 107 =
      83568107633699257892094114049935956361692390101849 := by
  rw [pow_two_pow_succ, u106]; decide
private theorem u108 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 108 =
      123698543662750492587502320311519995821276624445511 := by
  rw [pow_two_pow_succ, u107]; decide
private theorem u109 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 109 =
      200036701092858985488144830808561582147122820058988 := by
  rw [pow_two_pow_succ, u108]; decide
private theorem u110 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 110 =
      196719801384914925535881931128152738700201758420235 := by
  rw [pow_two_pow_succ, u109]; decide
private theorem u111 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 111 =
      31167195061008785711609152936400682446576660728055 := by
  rw [pow_two_pow_succ, u110]; decide
private theorem u112 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 112 =
      295032435233098707081310618330583395104073493381302 := by
  rw [pow_two_pow_succ, u111]; decide
private theorem u113 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 113 =
      286686663694913120078512541980556452727512796612216 := by
  rw [pow_two_pow_succ, u112]; decide
private theorem u114 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 114 =
      47977312602123053412125467041647255918628013875025 := by
  rw [pow_two_pow_succ, u113]; decide
private theorem u115 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 115 =
      25007420534888644394287740323469581947276938741232 := by
  rw [pow_two_pow_succ, u114]; decide
private theorem u116 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 116 =
      325494708046412688198202459681611998020219474633313 := by
  rw [pow_two_pow_succ, u115]; decide
private theorem u117 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 117 =
      122062066290587386533631630941886151630301914405694 := by
  rw [pow_two_pow_succ, u116]; decide
private theorem u118 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 118 =
      299988689398632432873397572271795507140775100934710 := by
  rw [pow_two_pow_succ, u117]; decide
private theorem u119 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 119 =
      200538559313453521572074216331982219035832527974207 := by
  rw [pow_two_pow_succ, u118]; decide
private theorem u120 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 120 =
      255950672132050405879453976781604276208628125295596 := by
  rw [pow_two_pow_succ, u119]; decide
private theorem u121 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 121 =
      139318910057325229749467683818483285417036001953996 := by
  rw [pow_two_pow_succ, u120]; decide
private theorem u122 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 122 =
      218028241209259214929338402535096146560619661187581 := by
  rw [pow_two_pow_succ, u121]; decide
private theorem u123 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 123 =
      260733780300223230547316219857775563801759604050877 := by
  rw [pow_two_pow_succ, u122]; decide
private theorem u124 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 124 =
      159794772241857003825277742610986820540893806207474 := by
  rw [pow_two_pow_succ, u123]; decide
private theorem u125 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 125 =
      241157185434297337611149883489830494500599374309829 := by
  rw [pow_two_pow_succ, u124]; decide
private theorem u126 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 126 =
      233054951755721669112185443398265716859266348591107 := by
  rw [pow_two_pow_succ, u125]; decide
private theorem u127 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 127 =
      343864723972211634234169339933846051930160125444096 := by
  rw [pow_two_pow_succ, u126]; decide
private theorem u128 :
    (286927782233639517182935977911655064918370995773952 : ZMod P) ^ (2:ℕ) ^ 128 =
      1 := by
  rw [pow_two_pow_succ, u127]; decide

private theorem cert_main : (3 : ZMod P) ^ (P - 1) = 1 := by
  rw [show P - 1 = 1010527601191 * 2 ^ 128 from by norm_num, pow_mul, hx, u128]

private theorem cert_q2 : (3 : ZMod P) ^ ((P - 1) / 2) ≠ 1 := by
  rw [show (P - 1) / 2 = 1010527601191 * 2 ^ 127 from by norm_num, pow_mul, hx, u127]
  decide

private theorem cert_qh : (3 : ZMod P) ^ ((P - 1) / 1010527601191) ≠ 1 := by
  rw [show (P - 1) / 1010527601191 = 2 ^ 128 from by norm_num, t128]
  decide

theorem prime_P : Nat.Prime P := by
  refine lucas_primality P 3 cert_main ?_
  intro q hq hdvd
  rw [show P - 1 = 1010527601191 * 2 ^ 128 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · have hqh : q = 1010527601191 :=
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
      218028241209259214929338402535096146560619661187581 := by
  rw [show (P - 1) / 64 = 1010527601191 * 2 ^ 122 from by norm_num, pow_mul, hx, u122]

/-- The order-64 certificate. -/
theorem orderOf_gP :
    orderOf (218028241209259214929338402535096146560619661187581 : ZMod P) = 64 := by
  have h5 : ¬ (218028241209259214929338402535096146560619661187581 : ZMod P) ^ (2:ℕ) ^ 5 = 1 := by
    decide
  have h6 : (218028241209259214929338402535096146560619661187581 : ZMod P) ^ (2:ℕ) ^ 6 = 1 := by
    decide
  have h := orderOf_eq_prime_pow
    (x := (218028241209259214929338402535096146560619661187581 : ZMod P)) h5 h6
  norm_num at h
  exact h

private theorem choose_64_13 : (64 : ℕ).choose 13 = 13136858812224 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_32_13 : (32 : ℕ).choose 13 = 347373600 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- **THE DEEP RUNG, UNCONDITIONAL**: `δ* = 51/64` exactly at `ε* = 2⁻¹²⁸` for the
dimension-12 (rate `3/16`) code on the 64-point smooth domain — the deepest-dimension,
closest-to-production-rate unconditional in-window pin to date. -/
theorem deltaStar_pin_mu6_dim12 :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode
          (218028241209259214929338402535096146560619661187581 : ZMod P) 64 11)
        (1 / 2 ^ 128)
      = 51 / 64 := by
  haveI : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have hP2 : 4 ^ (2 ^ (6 - 1) - 1) * (4 * 2 ^ (6 - 1)) ^ 2 ^ (6 - 1) < P ^ 2 := by
    show (4 : ℕ) ^ 31 * 128 ^ 32
        < 343864723972211634234169339933846051930160125444097 ^ 2
    norm_num
  have h6 : (1 : ℕ) ≤ 6 := by omega
  have hndvd :=
    ArkLib.ProximityGap.SharpThresholdDischarge.not_dvd_collisionResultant_of_sq_lt
    (p := P) (m := 6) (r := 13) h6 hP2
  have h := ArkLib.ProximityGap.Mu6ConditionalPin.kkh26_march_deltaStar_pin_of_not_dvd
    (p := P) (μ := 6) (r := 13)
    (g := (218028241209259214929338402535096146560619661187581 : ZMod P)) (n := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact orderOf_gP) (by norm_num)
    hndvd
    (1 / 2 ^ 128) ?hlo ?hhi
  case hlo =>
    have hc : ((64 : ℕ).choose 13 / 13 : ℕ) = 1010527600940 := by rw [choose_64_13]
    rw [hc]
    exact band_lo_general (by norm_num) (by norm_num)
  case hhi =>
    have hc : (2 ^ 13 * (2 ^ (6 - 1)).choose 13 : ℕ) = 2845684531200 := by
      show (2 ^ 13 * (32 : ℕ).choose 13 : ℕ) = 2845684531200
      rw [choose_32_13]
      norm_num
    rw [hc]
    exact band_hi_general (e := 2845684531199) (q := P) (by norm_num)
  rw [h]
  have e2 : (((13 : ℕ)) : ℝ≥0) = (13 : ℝ≥0) := by norm_num
  rw [e2]
  have hd : (13 : ℝ≥0) / ((2 : ℝ≥0) ^ 6) = 13 / 64 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

end ArkLib.ProximityGap.Mu6DeepRung

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.Mu6DeepRung.prime_P
#print axioms ArkLib.ProximityGap.Mu6DeepRung.orderOf_gP
#print axioms ArkLib.ProximityGap.Mu6DeepRung.deltaStar_pin_mu6_dim12
