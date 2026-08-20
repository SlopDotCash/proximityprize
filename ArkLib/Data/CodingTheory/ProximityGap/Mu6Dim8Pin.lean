/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Mu6ConditionalPin

/-!
# The μ = 6 dimension-8 (rate 1/8) literal-budget pin

`Mu6ConditionalPin.lean` lands the `r = 5` rung: a certified 149-bit Proth prime, an
order-64 generator, and the literal budget band `⌊C(64,5)/5⌋ ≤ ε*·p < 2^5·C(32,5)`, giving
`δ* = 59/64` at rate `1/16`.

This file lands the **next rung up in rate**, `r = 9`, on the same `μ = 6`, `n = 64`
smooth domain.  The band edges move to

* low  `⌊C(64,9)/9⌋  = 3060064945`
* high `2^9·C(32,9)  = 14360985600`

which is a genuinely different (and much narrower, in relative terms) window than the
`r = 5` one, so it needs its own certified prime.  We use the 160-bit Proth prime

`Q = 3060065077·2^128 + 1`

whose Proth coefficient `3060065077` is itself prime and sits inside the band.

The bad side is *free*: `collisionResultant_not_dvd_of_cyclotomicLandauSqBound` only asks
for `landauSqEnvelope (2^(μ-1)) < p^2`, and `landauSqEnvelope (2^5) = 2^255` does not
mention `r` at all.  Since `Q > 2^128`, the same already-proved analytic obligation
`cyclotomicLandauSqBound 6` discharges this rung too.

The resulting pin is at **rate 1/8** with `δ* = 55/64 = 0.859375`, which is

* strictly beyond the Johnson bound `1 - √(1/8) ≈ 0.646`, and
* strictly below capacity `1 - 1/8 = 0.875`.

## Main results

* `prime_Q` — Lucas certificate for the 160-bit Proth prime.
* `orderOf_gQ` — the order-64 generator certificate.
* `deltaStar_pin_mu6_dim8_of_not_dvd` — the conditional pin.
* `deltaStar_pin_mu6_dim8` — the unconditional pin, bad side discharged by
  `cyclotomicLandauSqBound_proved`.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ProximityGap.StaircaseBandTheorem

namespace ArkLib.ProximityGap.Mu6Dim8Pin

/-- The certified 160-bit Proth prime `Q = 3060065077·2^128 + 1`. -/
abbrev Q : ℕ := 1041286187333663812110313104770538564235256922113

private theorem pow_two_pow_succ {M : Type*} [Monoid M] (a : M) (k : ℕ) :
    a ^ (2:ℕ) ^ (k + 1) = (a ^ (2:ℕ) ^ k) ^ 2 := by
  rw [← pow_mul, ← pow_succ]

/-! ## Repeated-squaring chain for the base `3` -/

private theorem t0 : (3 : ZMod Q) ^ (2:ℕ) ^ 0 = 3 := by norm_num
private theorem t1 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 1 = 9 := by
  rw [pow_two_pow_succ, t0]; decide
private theorem t2 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 2 = 81 := by
  rw [pow_two_pow_succ, t1]; decide
private theorem t3 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 3 = 6561 := by
  rw [pow_two_pow_succ, t2]; decide
private theorem t4 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 4 = 43046721 := by
  rw [pow_two_pow_succ, t3]; decide
private theorem t5 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 5 = 1853020188851841 := by
  rw [pow_two_pow_succ, t4]; decide
private theorem t6 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 6 = 3433683820292512484657849089281 := by
  rw [pow_two_pow_succ, t5]; decide
private theorem t7 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 7 = 102864584821021272701016466989805294758697779455 := by
  rw [pow_two_pow_succ, t6]; decide
private theorem t8 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 8 = 404904054491562468100161922725726776951161925996 := by
  rw [pow_two_pow_succ, t7]; decide
private theorem t9 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 9 = 563256928467924697428632270792608662553539978236 := by
  rw [pow_two_pow_succ, t8]; decide
private theorem t10 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 10 = 789275750029947269898279674861469903014886720318 := by
  rw [pow_two_pow_succ, t9]; decide
private theorem t11 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 11 = 101988387373634798764427670552389157888712138656 := by
  rw [pow_two_pow_succ, t10]; decide
private theorem t12 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 12 = 1037754443758843850354001018298318525936776717987 := by
  rw [pow_two_pow_succ, t11]; decide
private theorem t13 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 13 = 735804778447298798022901142965905742767263538415 := by
  rw [pow_two_pow_succ, t12]; decide
private theorem t14 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 14 = 535499861507743223297909826597119911986158111010 := by
  rw [pow_two_pow_succ, t13]; decide
private theorem t15 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 15 = 39279078783930057802908575500288202532159840204 := by
  rw [pow_two_pow_succ, t14]; decide
private theorem t16 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 16 = 314535892373438378039991989607626365763581121284 := by
  rw [pow_two_pow_succ, t15]; decide
private theorem t17 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 17 = 910980576774695505901093801563836439567693242927 := by
  rw [pow_two_pow_succ, t16]; decide
private theorem t18 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 18 = 502487495040752040802727249600401325046496445409 := by
  rw [pow_two_pow_succ, t17]; decide
private theorem t19 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 19 = 670670054405505334827002713985697158128099715332 := by
  rw [pow_two_pow_succ, t18]; decide
private theorem t20 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 20 = 226671299049402753927476407209210243687258913541 := by
  rw [pow_two_pow_succ, t19]; decide
private theorem t21 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 21 = 739846707149954044368706640865122019468451146411 := by
  rw [pow_two_pow_succ, t20]; decide
private theorem t22 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 22 = 692584635060694080662281665889281433720654166780 := by
  rw [pow_two_pow_succ, t21]; decide
private theorem t23 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 23 = 932944691934691522719812985560256075907785332162 := by
  rw [pow_two_pow_succ, t22]; decide
private theorem t24 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 24 = 1038709198537474947572849426378071560568543421202 := by
  rw [pow_two_pow_succ, t23]; decide
private theorem t25 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 25 = 228478543486453441640529827595300847246794783096 := by
  rw [pow_two_pow_succ, t24]; decide
private theorem t26 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 26 = 527810996927708385984743054335847064082717300497 := by
  rw [pow_two_pow_succ, t25]; decide
private theorem t27 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 27 = 1026484744309119455492823815164656056755211240933 := by
  rw [pow_two_pow_succ, t26]; decide
private theorem t28 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 28 = 20904057028067454443313735692194518806614686436 := by
  rw [pow_two_pow_succ, t27]; decide
private theorem t29 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 29 = 116050178249600244649206572714510231157438885012 := by
  rw [pow_two_pow_succ, t28]; decide
private theorem t30 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 30 = 414168524853483588209621724272053336517237573553 := by
  rw [pow_two_pow_succ, t29]; decide
private theorem t31 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 31 = 325661314092913092831190607737564721370750179628 := by
  rw [pow_two_pow_succ, t30]; decide
private theorem t32 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 32 = 301483325974962745287496350042755388506247118696 := by
  rw [pow_two_pow_succ, t31]; decide
private theorem t33 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 33 = 751090708756513406912540622009613728311478446655 := by
  rw [pow_two_pow_succ, t32]; decide
private theorem t34 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 34 = 694273678537551189576741661619349202732565005195 := by
  rw [pow_two_pow_succ, t33]; decide
private theorem t35 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 35 = 743031460013359781107369521457583993308606114782 := by
  rw [pow_two_pow_succ, t34]; decide
private theorem t36 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 36 = 632683912649784674529857491094677914623448029591 := by
  rw [pow_two_pow_succ, t35]; decide
private theorem t37 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 37 = 104376820374011764948689921146940834037819738271 := by
  rw [pow_two_pow_succ, t36]; decide
private theorem t38 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 38 = 960668233623364936330198522451956226813050061790 := by
  rw [pow_two_pow_succ, t37]; decide
private theorem t39 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 39 = 285543012428157836808452921381909682320280312418 := by
  rw [pow_two_pow_succ, t38]; decide
private theorem t40 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 40 = 1029558417818988961933160212839951204208065215705 := by
  rw [pow_two_pow_succ, t39]; decide
private theorem t41 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 41 = 893751482787136849818616307715519001242500198815 := by
  rw [pow_two_pow_succ, t40]; decide
private theorem t42 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 42 = 396972036194747980126713702997556386348906343565 := by
  rw [pow_two_pow_succ, t41]; decide
private theorem t43 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 43 = 729821605549526722741919847290129634006257999744 := by
  rw [pow_two_pow_succ, t42]; decide
private theorem t44 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 44 = 113888644302635103268021813461138563562576850272 := by
  rw [pow_two_pow_succ, t43]; decide
private theorem t45 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 45 = 442325004267408676103123075421553357601912301951 := by
  rw [pow_two_pow_succ, t44]; decide
private theorem t46 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 46 = 913932607912411297934286542105681626186937834766 := by
  rw [pow_two_pow_succ, t45]; decide
private theorem t47 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 47 = 717030079197217293418038259443513395247632489876 := by
  rw [pow_two_pow_succ, t46]; decide
private theorem t48 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 48 = 155546458104246149680487611693294259007014180010 := by
  rw [pow_two_pow_succ, t47]; decide
private theorem t49 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 49 = 51489441615585279830966016569077553225544574267 := by
  rw [pow_two_pow_succ, t48]; decide
private theorem t50 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 50 = 223236042617007704014096096291495927111085347439 := by
  rw [pow_two_pow_succ, t49]; decide
private theorem t51 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 51 = 1022412200741974378786423890750297887763573428630 := by
  rw [pow_two_pow_succ, t50]; decide
private theorem t52 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 52 = 639341443100245788534087159966161334034432819631 := by
  rw [pow_two_pow_succ, t51]; decide
private theorem t53 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 53 = 815731739696056043222720598705346000395248884378 := by
  rw [pow_two_pow_succ, t52]; decide
private theorem t54 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 54 = 857831980970377398143159982206517767059513569336 := by
  rw [pow_two_pow_succ, t53]; decide
private theorem t55 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 55 = 791563048909418816709807429799986548720757357211 := by
  rw [pow_two_pow_succ, t54]; decide
private theorem t56 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 56 = 184486213925739932108460188319483298965433056719 := by
  rw [pow_two_pow_succ, t55]; decide
private theorem t57 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 57 = 859648347994875516528903182674414362903974961406 := by
  rw [pow_two_pow_succ, t56]; decide
private theorem t58 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 58 = 1040135621149440587864806548380905876984713394893 := by
  rw [pow_two_pow_succ, t57]; decide
private theorem t59 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 59 = 794081085695183961929054064788621639973113015897 := by
  rw [pow_two_pow_succ, t58]; decide
private theorem t60 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 60 = 134707210350842670702839899465584601450937173079 := by
  rw [pow_two_pow_succ, t59]; decide
private theorem t61 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 61 = 473030390683619191626016172450485304152423714657 := by
  rw [pow_two_pow_succ, t60]; decide
private theorem t62 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 62 = 640912547348365959435816586138110555969144417024 := by
  rw [pow_two_pow_succ, t61]; decide
private theorem t63 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 63 = 876341415594118067096059847346097288032985076765 := by
  rw [pow_two_pow_succ, t62]; decide
private theorem t64 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 64 = 1034099234832809531220957880010809592455746314877 := by
  rw [pow_two_pow_succ, t63]; decide
private theorem t65 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 65 = 543480715577437477408120779697046459500867487098 := by
  rw [pow_two_pow_succ, t64]; decide
private theorem t66 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 66 = 583723680475718787069268453380254391913691577251 := by
  rw [pow_two_pow_succ, t65]; decide
private theorem t67 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 67 = 551640034152289740498306253475286926007219590647 := by
  rw [pow_two_pow_succ, t66]; decide
private theorem t68 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 68 = 55140165514835380456557552767662316014904195902 := by
  rw [pow_two_pow_succ, t67]; decide
private theorem t69 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 69 = 299763188844942701337854460216710687961089632998 := by
  rw [pow_two_pow_succ, t68]; decide
private theorem t70 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 70 = 1823430076229461252134616708911101972271937154 := by
  rw [pow_two_pow_succ, t69]; decide
private theorem t71 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 71 = 946648180437073041872765661246238448303692403361 := by
  rw [pow_two_pow_succ, t70]; decide
private theorem t72 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 72 = 559047382672497483763195076481684196720408497407 := by
  rw [pow_two_pow_succ, t71]; decide
private theorem t73 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 73 = 431766999143552100495811088640958821340197759211 := by
  rw [pow_two_pow_succ, t72]; decide
private theorem t74 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 74 = 416670057344506512230809630607496257977282520802 := by
  rw [pow_two_pow_succ, t73]; decide
private theorem t75 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 75 = 478393444507139470126360496754170043120205456024 := by
  rw [pow_two_pow_succ, t74]; decide
private theorem t76 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 76 = 813254320026246050717388222276365793472574013813 := by
  rw [pow_two_pow_succ, t75]; decide
private theorem t77 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 77 = 152385451818181228350446613718056726049952393204 := by
  rw [pow_two_pow_succ, t76]; decide
private theorem t78 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 78 = 119088178877588144012605102098949070792479162834 := by
  rw [pow_two_pow_succ, t77]; decide
private theorem t79 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 79 = 26657227521096185051891828416021038452752754945 := by
  rw [pow_two_pow_succ, t78]; decide
private theorem t80 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 80 = 790759213839213503601037198317324248006643705148 := by
  rw [pow_two_pow_succ, t79]; decide
private theorem t81 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 81 = 1190590471237627433984029893882568575950369075 := by
  rw [pow_two_pow_succ, t80]; decide
private theorem t82 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 82 = 882016015886817240917094722985187977878648380896 := by
  rw [pow_two_pow_succ, t81]; decide
private theorem t83 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 83 = 430103816137438950292782134986525351997278017691 := by
  rw [pow_two_pow_succ, t82]; decide
private theorem t84 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 84 = 158991234569932775345299228798623461316561589544 := by
  rw [pow_two_pow_succ, t83]; decide
private theorem t85 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 85 = 161539709338844409590800685964096369671790132630 := by
  rw [pow_two_pow_succ, t84]; decide
private theorem t86 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 86 = 369705927165739665688732387584683108537574404263 := by
  rw [pow_two_pow_succ, t85]; decide
private theorem t87 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 87 = 209116174944904938609483397851539158675006691951 := by
  rw [pow_two_pow_succ, t86]; decide
private theorem t88 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 88 = 681287629587659932280643737144156680155938816500 := by
  rw [pow_two_pow_succ, t87]; decide
private theorem t89 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 89 = 799410520287168497693027059108267485794523202221 := by
  rw [pow_two_pow_succ, t88]; decide
private theorem t90 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 90 = 323453083989896147691377556795280168416122004612 := by
  rw [pow_two_pow_succ, t89]; decide
private theorem t91 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 91 = 870698436176209991018387088787898869392641627661 := by
  rw [pow_two_pow_succ, t90]; decide
private theorem t92 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 92 = 572952650244812569794526912073618102751558649712 := by
  rw [pow_two_pow_succ, t91]; decide
private theorem t93 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 93 = 288858806797726051752574663028184365517048671071 := by
  rw [pow_two_pow_succ, t92]; decide
private theorem t94 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 94 = 406053354949915908205581903403120201323708197936 := by
  rw [pow_two_pow_succ, t93]; decide
private theorem t95 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 95 = 572426486781009381934954468938077244228818723205 := by
  rw [pow_two_pow_succ, t94]; decide
private theorem t96 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 96 = 382296511840790970276574848447327068855540319963 := by
  rw [pow_two_pow_succ, t95]; decide
private theorem t97 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 97 = 402312904815922209816748930436919503726668779967 := by
  rw [pow_two_pow_succ, t96]; decide
private theorem t98 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 98 = 574039369509271370814231872661561899115676664792 := by
  rw [pow_two_pow_succ, t97]; decide
private theorem t99 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 99 = 981364776152998410496163676678740804711070749037 := by
  rw [pow_two_pow_succ, t98]; decide
private theorem t100 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 100 = 290390247912764086889736293081542776851502930108 := by
  rw [pow_two_pow_succ, t99]; decide
private theorem t101 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 101 = 7269508199498505598644816102011298384633444813 := by
  rw [pow_two_pow_succ, t100]; decide
private theorem t102 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 102 = 527650431093604291490025317658529954762713769024 := by
  rw [pow_two_pow_succ, t101]; decide
private theorem t103 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 103 = 174180120570991625284044642534763692379581625416 := by
  rw [pow_two_pow_succ, t102]; decide
private theorem t104 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 104 = 906392074871195462494905266615266109831606850416 := by
  rw [pow_two_pow_succ, t103]; decide
private theorem t105 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 105 = 46583171392911935115662047296215961729198488251 := by
  rw [pow_two_pow_succ, t104]; decide
private theorem t106 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 106 = 436664153751580372973066418935089872524401917499 := by
  rw [pow_two_pow_succ, t105]; decide
private theorem t107 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 107 = 789367970801847393620764075067106927457308184926 := by
  rw [pow_two_pow_succ, t106]; decide
private theorem t108 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 108 = 619569381386532245813259723190150930578185565522 := by
  rw [pow_two_pow_succ, t107]; decide
private theorem t109 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 109 = 71748318213565349071071498480092301556246440904 := by
  rw [pow_two_pow_succ, t108]; decide
private theorem t110 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 110 = 53678791034821291080762050414431494065063995957 := by
  rw [pow_two_pow_succ, t109]; decide
private theorem t111 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 111 = 536686658731035999460842803761091688693442234571 := by
  rw [pow_two_pow_succ, t110]; decide
private theorem t112 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 112 = 618671526714565848003109531582300124472616610186 := by
  rw [pow_two_pow_succ, t111]; decide
private theorem t113 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 113 = 1006752764176125706207882956203272265825714423931 := by
  rw [pow_two_pow_succ, t112]; decide
private theorem t114 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 114 = 113857875857051656304093606779170986823111805965 := by
  rw [pow_two_pow_succ, t113]; decide
private theorem t115 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 115 = 250107401724553433588776112235528885921435012420 := by
  rw [pow_two_pow_succ, t114]; decide
private theorem t116 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 116 = 347183840374423757669025937675940487450210601482 := by
  rw [pow_two_pow_succ, t115]; decide
private theorem t117 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 117 = 329401248303047247293520159982099564413713717068 := by
  rw [pow_two_pow_succ, t116]; decide
private theorem t118 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 118 = 870462670497821083468774817232281145731099556868 := by
  rw [pow_two_pow_succ, t117]; decide
private theorem t119 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 119 = 666720676061982586336223896887720982877085554238 := by
  rw [pow_two_pow_succ, t118]; decide
private theorem t120 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 120 = 582251527118932161162314929240628976838333271792 := by
  rw [pow_two_pow_succ, t119]; decide
private theorem t121 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 121 = 56469582823693128003986398693668487955369755746 := by
  rw [pow_two_pow_succ, t120]; decide
private theorem t122 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 122 = 247329870849105297414298806949597120652682218704 := by
  rw [pow_two_pow_succ, t121]; decide
private theorem t123 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 123 = 432745226415665849176050587390242397281113197201 := by
  rw [pow_two_pow_succ, t122]; decide
private theorem t124 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 124 = 1024786507293501166095686878306523729950187382333 := by
  rw [pow_two_pow_succ, t123]; decide
private theorem t125 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 125 = 449392236193629256763397782406139448339125677499 := by
  rw [pow_two_pow_succ, t124]; decide
private theorem t126 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 126 = 801313075121438480209220698564759471910591965554 := by
  rw [pow_two_pow_succ, t125]; decide
private theorem t127 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 127 = 824940743710519612199482210071349960590131720855 := by
  rw [pow_two_pow_succ, t126]; decide
private theorem t128 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 128 = 58740407591286412059566088223248853167444398167 := by
  rw [pow_two_pow_succ, t127]; decide

/-! ## The Proth coefficient power `3 ^ 3060065077` -/

private theorem hx :
    (3 : ZMod Q) ^ (3060065077:ℕ) =
      1027342024729392198413692922322366322532270007957 := by
  rw [show (3060065077:ℕ)
      = 2^31 + 2^29 + 2^28 + 2^26 + 2^25 + 2^22 + 2^21 + 2^18 + 2^15 + 2^14
        + 2^13 + 2^9 + 2^8 + 2^5 + 2^4 + 2^2 + 2^0
      from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    t31, t29, t28, t26, t25, t22, t21, t18, t15, t14, t13, t9, t8, t5, t4, t2, t0]
  decide

/-! ## Repeated-squaring chain for `x = 3 ^ 3060065077` -/

private theorem u0 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 0 =
      1027342024729392198413692922322366322532270007957 := by
  norm_num
private theorem u1 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 1 =
      208126290081206140753463087568855387660974277578 := by
  rw [pow_two_pow_succ, u0]; decide
private theorem u2 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 2 =
      812268734978882694054623934805398333157375030 := by
  rw [pow_two_pow_succ, u1]; decide
private theorem u3 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 3 =
      418409063745612387091563163716825107208720032730 := by
  rw [pow_two_pow_succ, u2]; decide
private theorem u4 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 4 =
      363779560939879889539797125492029333056246991968 := by
  rw [pow_two_pow_succ, u3]; decide
private theorem u5 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 5 =
      770430273912159977588013218066783743702203716458 := by
  rw [pow_two_pow_succ, u4]; decide
private theorem u6 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 6 =
      929088392631149138903684662837278338924437861681 := by
  rw [pow_two_pow_succ, u5]; decide
private theorem u7 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 7 =
      78583707402389852550855363515166213129198059913 := by
  rw [pow_two_pow_succ, u6]; decide
private theorem u8 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 8 =
      201447356812606266489204573282628675905121922003 := by
  rw [pow_two_pow_succ, u7]; decide
private theorem u9 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 9 =
      227929437725683139403256785259184796254645808968 := by
  rw [pow_two_pow_succ, u8]; decide
private theorem u10 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 10 =
      321802963703639582953740671455709193701855902973 := by
  rw [pow_two_pow_succ, u9]; decide
private theorem u11 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 11 =
      295540031194903436085772667476238491535583397519 := by
  rw [pow_two_pow_succ, u10]; decide
private theorem u12 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 12 =
      150008042194890512759472077609260510572873258116 := by
  rw [pow_two_pow_succ, u11]; decide
private theorem u13 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 13 =
      986299123583278031719378344104935038407991959242 := by
  rw [pow_two_pow_succ, u12]; decide
private theorem u14 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 14 =
      686477945139797821823643781963734865149473553147 := by
  rw [pow_two_pow_succ, u13]; decide
private theorem u15 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 15 =
      52548645842253040034314689670837354177652132179 := by
  rw [pow_two_pow_succ, u14]; decide
private theorem u16 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 16 =
      510532640023831814054876999946462530830687858794 := by
  rw [pow_two_pow_succ, u15]; decide
private theorem u17 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 17 =
      583730723469616689327885348890731081944527752786 := by
  rw [pow_two_pow_succ, u16]; decide
private theorem u18 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 18 =
      959092098259072876440594625709687706571697056617 := by
  rw [pow_two_pow_succ, u17]; decide
private theorem u19 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 19 =
      106376928340128141016299643345275538245907283357 := by
  rw [pow_two_pow_succ, u18]; decide
private theorem u20 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 20 =
      270798943608673251135350007138579932865122695734 := by
  rw [pow_two_pow_succ, u19]; decide
private theorem u21 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 21 =
      899261127484058176021865547073230484093850904471 := by
  rw [pow_two_pow_succ, u20]; decide
private theorem u22 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 22 =
      48988355904928848135525684012828981423680700231 := by
  rw [pow_two_pow_succ, u21]; decide
private theorem u23 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 23 =
      1014823557035490179182065205455915643056611503347 := by
  rw [pow_two_pow_succ, u22]; decide
private theorem u24 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 24 =
      515019235559800062125317965660291473921082355685 := by
  rw [pow_two_pow_succ, u23]; decide
private theorem u25 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 25 =
      65043643839183267633671123361306820948526690648 := by
  rw [pow_two_pow_succ, u24]; decide
private theorem u26 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 26 =
      932364335752222862644884527502955374227809153079 := by
  rw [pow_two_pow_succ, u25]; decide
private theorem u27 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 27 =
      132902223194507590824879510038266918028735530346 := by
  rw [pow_two_pow_succ, u26]; decide
private theorem u28 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 28 =
      424654803053411616188443136643128216912496397327 := by
  rw [pow_two_pow_succ, u27]; decide
private theorem u29 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 29 =
      412585244249293643277336830125718229057338134252 := by
  rw [pow_two_pow_succ, u28]; decide
private theorem u30 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 30 =
      472506768876085499895990738740957524397899710172 := by
  rw [pow_two_pow_succ, u29]; decide
private theorem u31 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 31 =
      990803157683764682711641764567425344700729207228 := by
  rw [pow_two_pow_succ, u30]; decide
private theorem u32 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 32 =
      518868495113885882499960120839749739982680483772 := by
  rw [pow_two_pow_succ, u31]; decide
private theorem u33 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 33 =
      1012640371909253373346109841635920362932582576642 := by
  rw [pow_two_pow_succ, u32]; decide
private theorem u34 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 34 =
      60045513154953000712006323639176922103999879036 := by
  rw [pow_two_pow_succ, u33]; decide
private theorem u35 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 35 =
      331908632471989176913020562933047956395938109894 := by
  rw [pow_two_pow_succ, u34]; decide
private theorem u36 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 36 =
      252222272939795668808967037108387682003617249183 := by
  rw [pow_two_pow_succ, u35]; decide
private theorem u37 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 37 =
      377327530495475579525898226462967004164921129974 := by
  rw [pow_two_pow_succ, u36]; decide
private theorem u38 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 38 =
      6056338474911275824567052989029850237264809550 := by
  rw [pow_two_pow_succ, u37]; decide
private theorem u39 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 39 =
      419839640645632381380365315378652455149606926213 := by
  rw [pow_two_pow_succ, u38]; decide
private theorem u40 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 40 =
      15161754395468340312151071527346111805818055935 := by
  rw [pow_two_pow_succ, u39]; decide
private theorem u41 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 41 =
      326797421887776962123054056752161551761477716592 := by
  rw [pow_two_pow_succ, u40]; decide
private theorem u42 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 42 =
      413129476970180363206953008320035795974145763493 := by
  rw [pow_two_pow_succ, u41]; decide
private theorem u43 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 43 =
      741348305744720889716216370366499420599287790718 := by
  rw [pow_two_pow_succ, u42]; decide
private theorem u44 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 44 =
      308568448305585956789501855424658585177386164350 := by
  rw [pow_two_pow_succ, u43]; decide
private theorem u45 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 45 =
      501641147532503764216726434226819460154471401779 := by
  rw [pow_two_pow_succ, u44]; decide
private theorem u46 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 46 =
      864137872991319875569651030147933863853672796879 := by
  rw [pow_two_pow_succ, u45]; decide
private theorem u47 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 47 =
      344681216883783239995150008878761760400989977837 := by
  rw [pow_two_pow_succ, u46]; decide
private theorem u48 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 48 =
      357317245268744915476444645481281330257872457129 := by
  rw [pow_two_pow_succ, u47]; decide
private theorem u49 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 49 =
      831154165498927467883349209942237743949596156161 := by
  rw [pow_two_pow_succ, u48]; decide
private theorem u50 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 50 =
      908876269234701194235826033407212240428479573420 := by
  rw [pow_two_pow_succ, u49]; decide
private theorem u51 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 51 =
      720270716396633627502428020898443021080326812584 := by
  rw [pow_two_pow_succ, u50]; decide
private theorem u52 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 52 =
      193350539539863241559924407483128337912727179463 := by
  rw [pow_two_pow_succ, u51]; decide
private theorem u53 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 53 =
      530529379935560883577398493289289208007494512602 := by
  rw [pow_two_pow_succ, u52]; decide
private theorem u54 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 54 =
      662339461612010499193220778382613720775882389470 := by
  rw [pow_two_pow_succ, u53]; decide
private theorem u55 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 55 =
      2910909358790779482591047366548455315737314624 := by
  rw [pow_two_pow_succ, u54]; decide
private theorem u56 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 56 =
      993283602197159395683264849491523713222553236148 := by
  rw [pow_two_pow_succ, u55]; decide
private theorem u57 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 57 =
      466596464332060131592118580082042758102701486475 := by
  rw [pow_two_pow_succ, u56]; decide
private theorem u58 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 58 =
      267125678300198607740449474329439188955594889705 := by
  rw [pow_two_pow_succ, u57]; decide
private theorem u59 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 59 =
      418675808309432881671767839976014537730403502502 := by
  rw [pow_two_pow_succ, u58]; decide
private theorem u60 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 60 =
      150017157801293802141368627853563506975123988331 := by
  rw [pow_two_pow_succ, u59]; decide
private theorem u61 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 61 =
      941472031262124229432240906357953932068980163289 := by
  rw [pow_two_pow_succ, u60]; decide
private theorem u62 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 62 =
      882303666474999327334189831337018109338877630685 := by
  rw [pow_two_pow_succ, u61]; decide
private theorem u63 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 63 =
      530808231481009295025666355895970193061538193637 := by
  rw [pow_two_pow_succ, u62]; decide
private theorem u64 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 64 =
      562798374701778147845313480969443966919037717066 := by
  rw [pow_two_pow_succ, u63]; decide
private theorem u65 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 65 =
      544911006312671407599701840157309071116987709587 := by
  rw [pow_two_pow_succ, u64]; decide
private theorem u66 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 66 =
      963313277400405137825653124405132190107960826152 := by
  rw [pow_two_pow_succ, u65]; decide
private theorem u67 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 67 =
      270507428332941876785469769836450355618132082725 := by
  rw [pow_two_pow_succ, u66]; decide
private theorem u68 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 68 =
      274019211173592009500039305712633288716937881364 := by
  rw [pow_two_pow_succ, u67]; decide
private theorem u69 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 69 =
      626635147246572645897081327579481992199681915332 := by
  rw [pow_two_pow_succ, u68]; decide
private theorem u70 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 70 =
      26667154758544839936063433294908850919890200772 := by
  rw [pow_two_pow_succ, u69]; decide
private theorem u71 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 71 =
      27669816882851080857112103576397253059655568936 := by
  rw [pow_two_pow_succ, u70]; decide
private theorem u72 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 72 =
      112584155170476179429366313002643252838826302409 := by
  rw [pow_two_pow_succ, u71]; decide
private theorem u73 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 73 =
      345063506983391892674034604250121361559853708799 := by
  rw [pow_two_pow_succ, u72]; decide
private theorem u74 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 74 =
      382580841789975156105123572215973154948869678757 := by
  rw [pow_two_pow_succ, u73]; decide
private theorem u75 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 75 =
      93229572064894950747792436860375264293756004058 := by
  rw [pow_two_pow_succ, u74]; decide
private theorem u76 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 76 =
      909351065857379579236793771976702477486917700504 := by
  rw [pow_two_pow_succ, u75]; decide
private theorem u77 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 77 =
      675212223906930043049110671220265829932586798915 := by
  rw [pow_two_pow_succ, u76]; decide
private theorem u78 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 78 =
      41113893944392083261411841011859638350317682740 := by
  rw [pow_two_pow_succ, u77]; decide
private theorem u79 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 79 =
      335706657743676737655560119641994849930578929735 := by
  rw [pow_two_pow_succ, u78]; decide
private theorem u80 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 80 =
      539608896872018699426068043142775953006342925254 := by
  rw [pow_two_pow_succ, u79]; decide
private theorem u81 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 81 =
      2607479974949881060745187952303782919186875358 := by
  rw [pow_two_pow_succ, u80]; decide
private theorem u82 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 82 =
      181058499910798744292733491343649165623405862140 := by
  rw [pow_two_pow_succ, u81]; decide
private theorem u83 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 83 =
      297312959585862278650134913499081203702718550874 := by
  rw [pow_two_pow_succ, u82]; decide
private theorem u84 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 84 =
      630374303095949382743504154071846121888780426796 := by
  rw [pow_two_pow_succ, u83]; decide
private theorem u85 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 85 =
      558168107980695572531552992338219825622771938917 := by
  rw [pow_two_pow_succ, u84]; decide
private theorem u86 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 86 =
      63579422080745019962773945647654495855599620230 := by
  rw [pow_two_pow_succ, u85]; decide
private theorem u87 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 87 =
      133071923619380987790273022426276592623076154376 := by
  rw [pow_two_pow_succ, u86]; decide
private theorem u88 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 88 =
      508685891426619092508975820429351878943329445802 := by
  rw [pow_two_pow_succ, u87]; decide
private theorem u89 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 89 =
      126319619532310693083750506306206377812986395588 := by
  rw [pow_two_pow_succ, u88]; decide
private theorem u90 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 90 =
      744219653635509803135993819204666109847519583161 := by
  rw [pow_two_pow_succ, u89]; decide
private theorem u91 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 91 =
      884794075008186610082445069433078451462957482664 := by
  rw [pow_two_pow_succ, u90]; decide
private theorem u92 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 92 =
      577231279854128277543185693528576039724296810183 := by
  rw [pow_two_pow_succ, u91]; decide
private theorem u93 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 93 =
      800803893953356711498928283741209568271500333941 := by
  rw [pow_two_pow_succ, u92]; decide
private theorem u94 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 94 =
      689540133494664400458473839087554962787122737201 := by
  rw [pow_two_pow_succ, u93]; decide
private theorem u95 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 95 =
      583968641013213967880111960386026818457830474473 := by
  rw [pow_two_pow_succ, u94]; decide
private theorem u96 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 96 =
      644501831436701859231798564489278455249566086059 := by
  rw [pow_two_pow_succ, u95]; decide
private theorem u97 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 97 =
      43981571399696638274593145212570595167396677501 := by
  rw [pow_two_pow_succ, u96]; decide
private theorem u98 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 98 =
      216900462951530324199014529657408432327145687323 := by
  rw [pow_two_pow_succ, u97]; decide
private theorem u99 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 99 =
      915596180772039085014897447277015095637058231744 := by
  rw [pow_two_pow_succ, u98]; decide
private theorem u100 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 100 =
      582384036348973982278619239610695853767443817394 := by
  rw [pow_two_pow_succ, u99]; decide
private theorem u101 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 101 =
      204709343183702806288014262342510034995859201981 := by
  rw [pow_two_pow_succ, u100]; decide
private theorem u102 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 102 =
      486718478213977367520166475681531517916137407168 := by
  rw [pow_two_pow_succ, u101]; decide
private theorem u103 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 103 =
      603175902345411415096582485897075666167134087001 := by
  rw [pow_two_pow_succ, u102]; decide
private theorem u104 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 104 =
      942314058930684308182215806011839049798961677323 := by
  rw [pow_two_pow_succ, u103]; decide
private theorem u105 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 105 =
      583621485149526500516708672014586278173917305329 := by
  rw [pow_two_pow_succ, u104]; decide
private theorem u106 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 106 =
      1001111794630807484828116318601988512970392773242 := by
  rw [pow_two_pow_succ, u105]; decide
private theorem u107 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 107 =
      638498047794608883115511615285353975563231692174 := by
  rw [pow_two_pow_succ, u106]; decide
private theorem u108 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 108 =
      648254144739100362568119720602526978522238485294 := by
  rw [pow_two_pow_succ, u107]; decide
private theorem u109 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 109 =
      44128319718059211415411649857574511437674623404 := by
  rw [pow_two_pow_succ, u108]; decide
private theorem u110 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 110 =
      512937630191718262075073385664210532936137985561 := by
  rw [pow_two_pow_succ, u109]; decide
private theorem u111 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 111 =
      406451214520384485834775095126892383776804647565 := by
  rw [pow_two_pow_succ, u110]; decide
private theorem u112 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 112 =
      8018610838839220832950476552816432305942435642 := by
  rw [pow_two_pow_succ, u111]; decide
private theorem u113 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 113 =
      904748399954251570298919360380221970289820946143 := by
  rw [pow_two_pow_succ, u112]; decide
private theorem u114 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 114 =
      57844962065195279815732746189317283593737942497 := by
  rw [pow_two_pow_succ, u113]; decide
private theorem u115 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 115 =
      21542587371038134890502140666845471415422572080 := by
  rw [pow_two_pow_succ, u114]; decide
private theorem u116 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 116 =
      2861256511852912005758125785392193264558436573 := by
  rw [pow_two_pow_succ, u115]; decide
private theorem u117 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 117 =
      322104034062392631701206026560307513664640526943 := by
  rw [pow_two_pow_succ, u116]; decide
private theorem u118 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 118 =
      87329695723196622591450739576565110429811744640 := by
  rw [pow_two_pow_succ, u117]; decide
private theorem u119 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 119 =
      244241695475372685825399084726131540877706531522 := by
  rw [pow_two_pow_succ, u118]; decide
private theorem u120 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 120 =
      524384141371748913203745543969092775851572802822 := by
  rw [pow_two_pow_succ, u119]; decide
private theorem u121 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 121 =
      198884688612578928399467069806916271101018989165 := by
  rw [pow_two_pow_succ, u120]; decide
private theorem u122 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 122 =
      11467558297445687940746688886579918959768545577 := by
  rw [pow_two_pow_succ, u121]; decide
private theorem u123 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 123 =
      225428623115928698393612602325878372534445935709 := by
  rw [pow_two_pow_succ, u122]; decide
private theorem u124 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 124 =
      387670523731929509272146382832021642701154166200 := by
  rw [pow_two_pow_succ, u123]; decide
private theorem u125 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 125 =
      578205260013069369343370250661294657336531067319 := by
  rw [pow_two_pow_succ, u124]; decide
private theorem u126 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 126 =
      695755858405374943409643109472959198309727808475 := by
  rw [pow_two_pow_succ, u125]; decide
private theorem u127 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 127 =
      1041286187333663812110313104770538564235256922112 := by
  rw [pow_two_pow_succ, u126]; decide
private theorem u128 :
    (1027342024729392198413692922322366322532270007957 : ZMod Q) ^ (2:ℕ) ^ 128 =
      1 := by
  rw [pow_two_pow_succ, u127]; decide

/-! ## The Lucas primality certificate -/

private theorem cert_main : (3 : ZMod Q) ^ (Q - 1) = 1 := by
  rw [show Q - 1 = 3060065077 * 2 ^ 128 from by norm_num, pow_mul, hx, u128]

private theorem cert_q2 : (3 : ZMod Q) ^ ((Q - 1) / 2) ≠ 1 := by
  rw [show (Q - 1) / 2 = 3060065077 * 2 ^ 127 from by norm_num, pow_mul, hx, u127]
  decide

private theorem cert_qh : (3 : ZMod Q) ^ ((Q - 1) / 3060065077) ≠ 1 := by
  rw [show (Q - 1) / 3060065077 = 2 ^ 128 from by norm_num, t128]
  decide

/-- **The 160-bit Proth prime certificate.** -/
theorem prime_Q : Nat.Prime Q := by
  refine lucas_primality Q 3 cert_main ?_
  intro q hq hdvd
  rw [show Q - 1 = 3060065077 * 2 ^ 128 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · have hqh : q = 3060065077 :=
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
    subst hqh
    exact cert_qh
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst hq2
    exact cert_q2

local instance fact_prime_Q : Fact (Nat.Prime Q) := ⟨prime_Q⟩

private theorem g_def :
    (3 : ZMod Q) ^ ((Q - 1) / 64) =
      11467558297445687940746688886579918959768545577 := by
  rw [show (Q - 1) / 64 = 3060065077 * 2 ^ 122 from by norm_num, pow_mul, hx, u122]

/-- The order-64 certificate for the dimension-8 rung. -/
theorem orderOf_gQ :
    orderOf (11467558297445687940746688886579918959768545577 : ZMod Q) = 64 := by
  have h5 : ¬ (11467558297445687940746688886579918959768545577 : ZMod Q) ^ (2:ℕ) ^ 5 = 1 := by
    decide
  have h6 : (11467558297445687940746688886579918959768545577 : ZMod Q) ^ (2:ℕ) ^ 6 = 1 := by
    decide
  have h := orderOf_eq_prime_pow
    (x := (11467558297445687940746688886579918959768545577 : ZMod Q)) h5 h6
  norm_num at h
  exact h

/-! ## The conditional pin -/

private theorem choose_64_9 : (64 : ℕ).choose 9 = 27540584512 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_32_9 : (32 : ℕ).choose 9 = 28048800 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- The certified prime `Q` **inhabits** the `r = 9` literal-budget band.

`Mu6LiteralBands.mu6_band_open_r9` proves that this band is nonempty
(`C(64,9)/9 < 2^9·C(32,9)`); this lemma exhibits an actual certified prime inside it,
which is what the pin below consumes. -/
theorem Q_mem_band_r9 :
    (2 ^ 6).choose 9 / 9 * 2 ^ 128 ≤ Q ∧ Q < 2 ^ 9 * (2 ^ 5).choose 9 * 2 ^ 128 := by
  refine ⟨?_, ?_⟩
  · have h : (2 ^ 6 : ℕ).choose 9 / 9 = 3060064945 := by
      rw [show (2 ^ 6 : ℕ) = 64 from by norm_num, choose_64_9]
    rw [h]; norm_num
  · have h : (2 ^ 9 : ℕ) * (2 ^ 5 : ℕ).choose 9 = 14360985600 := by
      rw [show (2 ^ 5 : ℕ) = 32 from by norm_num, choose_32_9]
      norm_num
    rw [h]; norm_num

/-- **The μ = 6 conditional literal-budget pin at rate 1/8**: given only the in-tree
divisibility hypothesis, `δ* = 55/64` exactly at `ε* = 2⁻¹²⁸` for the dimension-8
(rate `1/8`) code on the 64-point smooth domain — beyond Johnson (`1 - √(1/8) ≈ 0.646`),
below capacity (`7/8`). -/
theorem deltaStar_pin_mu6_dim8_of_not_dvd
    (hndvd : ∀ d₁ ∈ sigData (2 ^ 5) 9, ∀ d₂ ∈ sigData (2 ^ 5) 9,
      d₁ ≠ d₂ → ¬ (Q : ℤ) ∣ collisionResultant 6 d₁ d₂) :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (11467558297445687940746688886579918959768545577 : ZMod Q) 64 7)
        (1 / 2 ^ 128)
      = 55 / 64 := by
  haveI : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have h := Mu6ConditionalPin.kkh26_march_deltaStar_pin_of_not_dvd (p := Q) (μ := 6) (r := 9)
    (g := (11467558297445687940746688886579918959768545577 : ZMod Q)) (n := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact orderOf_gQ) (by norm_num) hndvd
    (1 / 2 ^ 128) ?hlo ?hhi
  case hlo =>
    have hc : ((64 : ℕ).choose 9 / 9 : ℕ) = 3060064945 := by rw [choose_64_9]
    rw [hc]
    exact band_lo_general (by norm_num) (by norm_num)
  case hhi =>
    have hc : (2 ^ 9 * (2 ^ (6 - 1)).choose 9 : ℕ) = 14360985600 := by
      change (2 ^ 9 * (32 : ℕ).choose 9 : ℕ) = 14360985600
      rw [choose_32_9]
      norm_num
    rw [hc]
    exact band_hi_general (e := 14360985599) (q := Q) (by norm_num)
  rw [h]
  have e2 : (((9 : ℕ)) : ℝ≥0) = (9 : ℝ≥0) := by norm_num
  rw [e2]
  have hd : (9 : ℝ≥0) / ((2 : ℝ≥0) ^ 6) = 9 / 64 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- **Mahler/Landau handoff.**  If every relevant collision resultant has absolute value
below the certified prime `Q`, the named divisibility hypothesis is discharged. -/
theorem deltaStar_pin_mu6_dim8_of_collisionResultant_natAbs_lt
    (hbound : ∀ d₁ ∈ sigData (2 ^ 5) 9, ∀ d₂ ∈ sigData (2 ^ 5) 9,
      d₁ ≠ d₂ → (collisionResultant 6 d₁ d₂).natAbs < Q) :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (11467558297445687940746688886579918959768545577 : ZMod Q) 64 7)
        (1 / 2 ^ 128)
      = 55 / 64 := by
  exact deltaStar_pin_mu6_dim8_of_not_dvd
    (collisionResultant_not_dvd_of_forall_natAbs_lt (p := Q) (m := 6) (r := 9)
      (by omega) hbound)

/-- The certified prime `Q` clears the μ = 6 squared Landau envelope `2^255 < Q^2`.
Note the envelope does not depend on `r`, which is why this rung reuses the `r = 5`
analytic input verbatim. -/
theorem landauSqEnvelope_mu6_lt_Q_sq : landauSqEnvelope (2 ^ 5) < Q ^ 2 := by
  have hstrict : landauSqEnvelope (2 ^ 5) < (2 ^ 128 : ℕ) ^ 2 := by
    rw [Mu6ConditionalPin.landauSqEnvelope_mu6_eq_two_pow_255]
    norm_num
  have hq : 2 ^ 128 ≤ Q := by norm_num [Q]
  exact lt_of_lt_of_le hstrict (Nat.pow_le_pow_left hq 2)

/-- **Squared Mahler/Landau handoff for the rate-1/8 rung.** -/
theorem deltaStar_pin_mu6_dim8_of_collisionResultant_natAbs_sq_bound
    (hbound : ∀ d₁ ∈ sigData (2 ^ 5) 9, ∀ d₂ ∈ sigData (2 ^ 5) 9,
      d₁ ≠ d₂ → (collisionResultant 6 d₁ d₂).natAbs ^ 2 ≤ landauSqEnvelope (2 ^ 5)) :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (11467558297445687940746688886579918959768545577 : ZMod Q) 64 7)
        (1 / 2 ^ 128)
      = 55 / 64 := by
  exact deltaStar_pin_mu6_dim8_of_not_dvd
    (collisionResultant_not_dvd_of_uniform_natAbs_sq_bound (p := Q)
      (B := landauSqEnvelope (2 ^ 5)) (m := 6) (r := 9) (by norm_num)
      hbound landauSqEnvelope_mu6_lt_Q_sq)

/-- **Cyclotomic Landau handoff for the rate-1/8 rung.** -/
theorem deltaStar_pin_mu6_dim8_of_cyclotomicLandauSqBound
    (hL : cyclotomicLandauSqBound 6) :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (11467558297445687940746688886579918959768545577 : ZMod Q) 64 7)
        (1 / 2 ^ 128)
      = 55 / 64 := by
  exact deltaStar_pin_mu6_dim8_of_not_dvd
    (collisionResultant_not_dvd_of_cyclotomicLandauSqBound (p := Q)
      (m := 6) (r := 9) hL (by norm_num) (by norm_num)
      landauSqEnvelope_mu6_lt_Q_sq)

/-- **Promoted μ = 6 dimension-8 literal pin.**  `δ* = 55/64` at `ε* = 2^-128` for the
rate-`1/8` code on the 64-point smooth domain, with no remaining named hypothesis. -/
theorem deltaStar_pin_mu6_dim8 :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (11467558297445687940746688886579918959768545577 : ZMod Q) 64 7)
        (1 / 2 ^ 128)
      = 55 / 64 := by
  exact deltaStar_pin_mu6_dim8_of_cyclotomicLandauSqBound
    (cyclotomicLandauSqBound_proved (m := 6) (by norm_num))

/-- The Mahler/Landau target `2^143` is strictly below the certified prime `Q`. -/
theorem two_pow_143_lt_Q : (2 : ℕ) ^ 143 < Q := by
  have hpow : (2 : ℕ) ^ 143 = 2 ^ 15 * 2 ^ 128 := by
    rw [show 143 = 15 + 128 by norm_num, pow_add]
  have hcoeff : (2 : ℕ) ^ 15 < 3060065077 := by norm_num
  have hscaled : (2 : ℕ) ^ 15 * 2 ^ 128 < 3060065077 * 2 ^ 128 :=
    Nat.mul_lt_mul_of_pos_right hcoeff (by positivity)
  have hQm1 : Q - 1 = 3060065077 * 2 ^ 128 := by norm_num
  rw [hpow]
  omega

#print axioms ArkLib.ProximityGap.Mu6Dim8Pin.prime_Q
#print axioms ArkLib.ProximityGap.Mu6Dim8Pin.Q_mem_band_r9
#print axioms ArkLib.ProximityGap.Mu6Dim8Pin.orderOf_gQ
#print axioms ArkLib.ProximityGap.Mu6Dim8Pin.deltaStar_pin_mu6_dim8_of_not_dvd
#print axioms ArkLib.ProximityGap.Mu6Dim8Pin.landauSqEnvelope_mu6_lt_Q_sq
#print axioms ArkLib.ProximityGap.Mu6Dim8Pin.deltaStar_pin_mu6_dim8
#print axioms ArkLib.ProximityGap.Mu6Dim8Pin.two_pow_143_lt_Q

end ArkLib.ProximityGap.Mu6Dim8Pin
