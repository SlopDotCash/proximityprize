/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch
import Mathlib.NumberTheory.LucasPrimality

/-!
# The certified `2^80` prime and the four μ = 5 rungs (#371, round-6 synthesis item 3)

The round-6 synthesis left the `μ = 5` rungs `r = 7, 8, 9` "band-ready, blocked only on a
certified prime `p > 2^80`, `p ≡ 1 (mod 32)`".  This file supplies the prime and lands the
rungs — plus the `r = 10` rung of `march_opens_r10_mu5`.

**The prime.**  `P = 65581·2^64 + 1 = 1209755923097946104528897 ≈ 2^80.0009` — Proth shape,
so `P − 1 = h·2^64` with `h = 65581` prime and the Lucas certificate (`lucas_primality`)
needs exactly two cofactor checks (`q = 2`, `q = h`), with witness `a = 3`.

**The method (kernel-cheap certificates).**  A naive `decide` on `3^(P−1) = 1` would unfold
`npowRec` for `2^80` steps.  Instead: *literal squaring chains* — `t_k = 3^(2^k)` and
`u_k = (3^h)^(2^k)` as ~130 generated one-multiplication `decide` steps on concrete
residues, glued by `pow_two_pow_succ : a^(2^(k+1)) = (a^(2^k))^2` and assembled by
`pow_mul`/`pow_add` algebra.  Every kernel step is a single bignum `mulmod`.  This is the
reusable pattern for all future big-field instances (production shape needs `q ≥ 2^128+`).

**The order-32 element.**  `g = 3^((P−1)/32) = u_59 = 350966889535864008599609`;
`g^16 = u_63 ≠ 1`, `g^32 = u_64 = 1` give `orderOf g = 32` by `orderOf_eq_prime_pow`.

**The four new pins** (`kkh26_march_deltaStar_pin` instances, dimensions 6–9, all beyond
Johnson `r² < (r−1)·32`, all below capacity):

| r | dim | rate | ε*·P | ceiling count | δ* |
|---|-----|------|------|---------------|----|
| 7 | 6 | 6/32 | 480836 | 1464320 | **25/32** |
| 8 | 7 | 7/32 | 1314787 | 3294720 | **3/4** |
| 9 | 8 | 8/32 | 3116533 | 5857280 | **23/32** |
| 10 | 9 | 9/32 | 6451224 | 8200192 | **11/16** |

Probe: the chain literals, the Lucas witness, and the band counts are generated and
cross-checked by `scripts/probes/probe_certified_rung_prime.py` (deterministic Miller–Rabin
for `p < 3.3·10^24`, plus the exact `pow`-chain replay).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction

namespace ArkLib.ProximityGap.CertifiedRungPrime

/-- The certified prime `65581·2^64 + 1`. -/
abbrev P : ℕ := 1209755923097946104528897

/-- Squaring-chain glue: `a^(2^(k+1)) = (a^(2^k))^2`. -/
private theorem pow_two_pow_succ {M : Type} [Monoid M] (a : M) (k : ℕ) :
    a ^ (2:ℕ) ^ (k + 1) = (a ^ (2:ℕ) ^ k) ^ 2 := by
  rw [← pow_mul]
  congr 1

/-! ### The `t`-chain: `t_k = 3^(2^k)` in `ZMod P` -/

private theorem t0 : (3 : ZMod P) ^ (2:ℕ) ^ 0 = 3 := by norm_num
private theorem t1 : (3 : ZMod P) ^ (2:ℕ) ^ 1 = 9 := by
  rw [pow_two_pow_succ, t0]; decide
private theorem t2 : (3 : ZMod P) ^ (2:ℕ) ^ 2 = 81 := by
  rw [pow_two_pow_succ, t1]; decide
private theorem t3 : (3 : ZMod P) ^ (2:ℕ) ^ 3 = 6561 := by
  rw [pow_two_pow_succ, t2]; decide
private theorem t4 : (3 : ZMod P) ^ (2:ℕ) ^ 4 = 43046721 := by
  rw [pow_two_pow_succ, t3]; decide
private theorem t5 : (3 : ZMod P) ^ (2:ℕ) ^ 5 = 1853020188851841 := by
  rw [pow_two_pow_succ, t4]; decide
private theorem t6 : (3 : ZMod P) ^ (2:ℕ) ^ 6 = 920353688411628658453962 := by
  rw [pow_two_pow_succ, t5]; decide
private theorem t7 : (3 : ZMod P) ^ (2:ℕ) ^ 7 = 18984844597147418432106 := by
  rw [pow_two_pow_succ, t6]; decide
private theorem t8 : (3 : ZMod P) ^ (2:ℕ) ^ 8 = 974572391404488699657388 := by
  rw [pow_two_pow_succ, t7]; decide
private theorem t9 : (3 : ZMod P) ^ (2:ℕ) ^ 9 = 118484389273303341362598 := by
  rw [pow_two_pow_succ, t8]; decide
private theorem t10 : (3 : ZMod P) ^ (2:ℕ) ^ 10 = 475934671803664628069960 := by
  rw [pow_two_pow_succ, t9]; decide
private theorem t11 : (3 : ZMod P) ^ (2:ℕ) ^ 11 = 1126418346183669561337414 := by
  rw [pow_two_pow_succ, t10]; decide
private theorem t12 : (3 : ZMod P) ^ (2:ℕ) ^ 12 = 873999692696330404882241 := by
  rw [pow_two_pow_succ, t11]; decide
private theorem t13 : (3 : ZMod P) ^ (2:ℕ) ^ 13 = 33189402755948891452018 := by
  rw [pow_two_pow_succ, t12]; decide
private theorem t14 : (3 : ZMod P) ^ (2:ℕ) ^ 14 = 106522800794641564668010 := by
  rw [pow_two_pow_succ, t13]; decide
private theorem t15 : (3 : ZMod P) ^ (2:ℕ) ^ 15 = 240604703944086077809938 := by
  rw [pow_two_pow_succ, t14]; decide
private theorem t16 : (3 : ZMod P) ^ (2:ℕ) ^ 16 = 207886361740629323845736 := by
  rw [pow_two_pow_succ, t15]; decide
private theorem t17 : (3 : ZMod P) ^ (2:ℕ) ^ 17 = 491589236840060353989760 := by
  rw [pow_two_pow_succ, t16]; decide
private theorem t18 : (3 : ZMod P) ^ (2:ℕ) ^ 18 = 156627822115117005572578 := by
  rw [pow_two_pow_succ, t17]; decide
private theorem t19 : (3 : ZMod P) ^ (2:ℕ) ^ 19 = 46545914956388155948672 := by
  rw [pow_two_pow_succ, t18]; decide
private theorem t20 : (3 : ZMod P) ^ (2:ℕ) ^ 20 = 170186300172897461031981 := by
  rw [pow_two_pow_succ, t19]; decide
private theorem t21 : (3 : ZMod P) ^ (2:ℕ) ^ 21 = 956127516072153085962152 := by
  rw [pow_two_pow_succ, t20]; decide
private theorem t22 : (3 : ZMod P) ^ (2:ℕ) ^ 22 = 14608565144294237027594 := by
  rw [pow_two_pow_succ, t21]; decide
private theorem t23 : (3 : ZMod P) ^ (2:ℕ) ^ 23 = 580398493032556636477798 := by
  rw [pow_two_pow_succ, t22]; decide
private theorem t24 : (3 : ZMod P) ^ (2:ℕ) ^ 24 = 192011901004249331703294 := by
  rw [pow_two_pow_succ, t23]; decide
private theorem t25 : (3 : ZMod P) ^ (2:ℕ) ^ 25 = 1062944913614290006310008 := by
  rw [pow_two_pow_succ, t24]; decide
private theorem t26 : (3 : ZMod P) ^ (2:ℕ) ^ 26 = 514868239999814258221831 := by
  rw [pow_two_pow_succ, t25]; decide
private theorem t27 : (3 : ZMod P) ^ (2:ℕ) ^ 27 = 1150963697269867463233864 := by
  rw [pow_two_pow_succ, t26]; decide
private theorem t28 : (3 : ZMod P) ^ (2:ℕ) ^ 28 = 69337193528593490456218 := by
  rw [pow_two_pow_succ, t27]; decide
private theorem t29 : (3 : ZMod P) ^ (2:ℕ) ^ 29 = 1039028285266755147928789 := by
  rw [pow_two_pow_succ, t28]; decide
private theorem t30 : (3 : ZMod P) ^ (2:ℕ) ^ 30 = 779996612502908526930191 := by
  rw [pow_two_pow_succ, t29]; decide
private theorem t31 : (3 : ZMod P) ^ (2:ℕ) ^ 31 = 735872103709237088167414 := by
  rw [pow_two_pow_succ, t30]; decide
private theorem t32 : (3 : ZMod P) ^ (2:ℕ) ^ 32 = 23564241571573610038503 := by
  rw [pow_two_pow_succ, t31]; decide
private theorem t33 : (3 : ZMod P) ^ (2:ℕ) ^ 33 = 997711603698359840462240 := by
  rw [pow_two_pow_succ, t32]; decide
private theorem t34 : (3 : ZMod P) ^ (2:ℕ) ^ 34 = 945940523702405476674184 := by
  rw [pow_two_pow_succ, t33]; decide
private theorem t35 : (3 : ZMod P) ^ (2:ℕ) ^ 35 = 425345621471965373770105 := by
  rw [pow_two_pow_succ, t34]; decide
private theorem t36 : (3 : ZMod P) ^ (2:ℕ) ^ 36 = 754831904391108156168847 := by
  rw [pow_two_pow_succ, t35]; decide
private theorem t37 : (3 : ZMod P) ^ (2:ℕ) ^ 37 = 876663324816556033122324 := by
  rw [pow_two_pow_succ, t36]; decide
private theorem t38 : (3 : ZMod P) ^ (2:ℕ) ^ 38 = 1172551983027581615210852 := by
  rw [pow_two_pow_succ, t37]; decide
private theorem t39 : (3 : ZMod P) ^ (2:ℕ) ^ 39 = 999116455523751684700931 := by
  rw [pow_two_pow_succ, t38]; decide
private theorem t40 : (3 : ZMod P) ^ (2:ℕ) ^ 40 = 1006084672189266832518590 := by
  rw [pow_two_pow_succ, t39]; decide
private theorem t41 : (3 : ZMod P) ^ (2:ℕ) ^ 41 = 371225140962831388656109 := by
  rw [pow_two_pow_succ, t40]; decide
private theorem t42 : (3 : ZMod P) ^ (2:ℕ) ^ 42 = 547403953723532418374809 := by
  rw [pow_two_pow_succ, t41]; decide
private theorem t43 : (3 : ZMod P) ^ (2:ℕ) ^ 43 = 512747018561730313692545 := by
  rw [pow_two_pow_succ, t42]; decide
private theorem t44 : (3 : ZMod P) ^ (2:ℕ) ^ 44 = 221436494537990348743481 := by
  rw [pow_two_pow_succ, t43]; decide
private theorem t45 : (3 : ZMod P) ^ (2:ℕ) ^ 45 = 261531558086583878431820 := by
  rw [pow_two_pow_succ, t44]; decide
private theorem t46 : (3 : ZMod P) ^ (2:ℕ) ^ 46 = 1000228260176270110845707 := by
  rw [pow_two_pow_succ, t45]; decide
private theorem t47 : (3 : ZMod P) ^ (2:ℕ) ^ 47 = 803505849773522966312284 := by
  rw [pow_two_pow_succ, t46]; decide
private theorem t48 : (3 : ZMod P) ^ (2:ℕ) ^ 48 = 815128540463719579216921 := by
  rw [pow_two_pow_succ, t47]; decide
private theorem t49 : (3 : ZMod P) ^ (2:ℕ) ^ 49 = 696311436326498221603930 := by
  rw [pow_two_pow_succ, t48]; decide
private theorem t50 : (3 : ZMod P) ^ (2:ℕ) ^ 50 = 129261119478689455798151 := by
  rw [pow_two_pow_succ, t49]; decide
private theorem t51 : (3 : ZMod P) ^ (2:ℕ) ^ 51 = 544373049270766214475520 := by
  rw [pow_two_pow_succ, t50]; decide
private theorem t52 : (3 : ZMod P) ^ (2:ℕ) ^ 52 = 1151806823526317406819366 := by
  rw [pow_two_pow_succ, t51]; decide
private theorem t53 : (3 : ZMod P) ^ (2:ℕ) ^ 53 = 360642083790541242591729 := by
  rw [pow_two_pow_succ, t52]; decide
private theorem t54 : (3 : ZMod P) ^ (2:ℕ) ^ 54 = 1072694845567928060390961 := by
  rw [pow_two_pow_succ, t53]; decide
private theorem t55 : (3 : ZMod P) ^ (2:ℕ) ^ 55 = 876650097609150976651451 := by
  rw [pow_two_pow_succ, t54]; decide
private theorem t56 : (3 : ZMod P) ^ (2:ℕ) ^ 56 = 280745832173397774627179 := by
  rw [pow_two_pow_succ, t55]; decide
private theorem t57 : (3 : ZMod P) ^ (2:ℕ) ^ 57 = 688427316103398438525134 := by
  rw [pow_two_pow_succ, t56]; decide
private theorem t58 : (3 : ZMod P) ^ (2:ℕ) ^ 58 = 938245176106200323588608 := by
  rw [pow_two_pow_succ, t57]; decide
private theorem t59 : (3 : ZMod P) ^ (2:ℕ) ^ 59 = 171151430696875851717236 := by
  rw [pow_two_pow_succ, t58]; decide
private theorem t60 : (3 : ZMod P) ^ (2:ℕ) ^ 60 = 639090928428348776223024 := by
  rw [pow_two_pow_succ, t59]; decide
private theorem t61 : (3 : ZMod P) ^ (2:ℕ) ^ 61 = 228869521599978114272775 := by
  rw [pow_two_pow_succ, t60]; decide
private theorem t62 : (3 : ZMod P) ^ (2:ℕ) ^ 62 = 154591024794234715596254 := by
  rw [pow_two_pow_succ, t61]; decide
private theorem t63 : (3 : ZMod P) ^ (2:ℕ) ^ 63 = 279152482440584968849244 := by
  rw [pow_two_pow_succ, t62]; decide
private theorem t64 : (3 : ZMod P) ^ (2:ℕ) ^ 64 = 203767384680505980782152 := by
  rw [pow_two_pow_succ, t63]; decide

/-! ### `x = 3^65581` (binary: `2^16 + 2^5 + 2^3 + 2^2 + 1`) -/

private theorem hx : (3 : ZMod P) ^ (65581:ℕ) = 698383666586983511969729 := by
  rw [show (65581:ℕ) = 2^16 + 2^5 + 2^3 + 2^2 + 1 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_one, t16, t5, t3, t2]
  decide

/-! ### The `u`-chain: `u_k = x^(2^k)` -/

private theorem u0 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 0 = 698383666586983511969729 := by norm_num
private theorem u1 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 1 = 642605398188380223768137 := by
  rw [pow_two_pow_succ, u0]; decide
private theorem u2 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 2 = 1080408286383897541814489 := by
  rw [pow_two_pow_succ, u1]; decide
private theorem u3 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 3 = 949646118163682354041069 := by
  rw [pow_two_pow_succ, u2]; decide
private theorem u4 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 4 = 206871562327763578509293 := by
  rw [pow_two_pow_succ, u3]; decide
private theorem u5 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 5 = 727825716028331247438494 := by
  rw [pow_two_pow_succ, u4]; decide
private theorem u6 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 6 = 740558226461426691496422 := by
  rw [pow_two_pow_succ, u5]; decide
private theorem u7 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 7 = 1053886906334746898243282 := by
  rw [pow_two_pow_succ, u6]; decide
private theorem u8 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 8 = 947680991024325234452284 := by
  rw [pow_two_pow_succ, u7]; decide
private theorem u9 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 9 = 898201061522433358811730 := by
  rw [pow_two_pow_succ, u8]; decide
private theorem u10 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 10 = 734164157290677768984723 := by
  rw [pow_two_pow_succ, u9]; decide
private theorem u11 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 11 = 15459220611609899751481 := by
  rw [pow_two_pow_succ, u10]; decide
private theorem u12 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 12 = 538863318273018555250732 := by
  rw [pow_two_pow_succ, u11]; decide
private theorem u13 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 13 = 160026030475005863303614 := by
  rw [pow_two_pow_succ, u12]; decide
private theorem u14 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 14 = 474102715912610316020294 := by
  rw [pow_two_pow_succ, u13]; decide
private theorem u15 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 15 = 641633199053244879108825 := by
  rw [pow_two_pow_succ, u14]; decide
private theorem u16 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 16 = 516163151566440638741542 := by
  rw [pow_two_pow_succ, u15]; decide
private theorem u17 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 17 = 1138020162022295365053914 := by
  rw [pow_two_pow_succ, u16]; decide
private theorem u18 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 18 = 414260708726950589324899 := by
  rw [pow_two_pow_succ, u17]; decide
private theorem u19 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 19 = 227129609295912077709811 := by
  rw [pow_two_pow_succ, u18]; decide
private theorem u20 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 20 = 722218973361590163055488 := by
  rw [pow_two_pow_succ, u19]; decide
private theorem u21 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 21 = 630326316953098456199503 := by
  rw [pow_two_pow_succ, u20]; decide
private theorem u22 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 22 = 522896205912070649077508 := by
  rw [pow_two_pow_succ, u21]; decide
private theorem u23 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 23 = 486412808929137484496328 := by
  rw [pow_two_pow_succ, u22]; decide
private theorem u24 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 24 = 60989790323684907674028 := by
  rw [pow_two_pow_succ, u23]; decide
private theorem u25 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 25 = 879981499087535516959592 := by
  rw [pow_two_pow_succ, u24]; decide
private theorem u26 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 26 = 149222087687574788092943 := by
  rw [pow_two_pow_succ, u25]; decide
private theorem u27 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 27 = 794963812104110496600891 := by
  rw [pow_two_pow_succ, u26]; decide
private theorem u28 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 28 = 195790607492879124788656 := by
  rw [pow_two_pow_succ, u27]; decide
private theorem u29 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 29 = 1113767968824876081416397 := by
  rw [pow_two_pow_succ, u28]; decide
private theorem u30 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 30 = 996775905366244009849945 := by
  rw [pow_two_pow_succ, u29]; decide
private theorem u31 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 31 = 1097407342016991270055085 := by
  rw [pow_two_pow_succ, u30]; decide
private theorem u32 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 32 = 947099164230633769707841 := by
  rw [pow_two_pow_succ, u31]; decide
private theorem u33 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 33 = 386490315459872036354206 := by
  rw [pow_two_pow_succ, u32]; decide
private theorem u34 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 34 = 662107470594159461178200 := by
  rw [pow_two_pow_succ, u33]; decide
private theorem u35 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 35 = 241424487965570338269697 := by
  rw [pow_two_pow_succ, u34]; decide
private theorem u36 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 36 = 789102568068526947090095 := by
  rw [pow_two_pow_succ, u35]; decide
private theorem u37 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 37 = 874468722758490949431389 := by
  rw [pow_two_pow_succ, u36]; decide
private theorem u38 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 38 = 565794869451702014142395 := by
  rw [pow_two_pow_succ, u37]; decide
private theorem u39 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 39 = 495198525842622734650050 := by
  rw [pow_two_pow_succ, u38]; decide
private theorem u40 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 40 = 446717896677192036483545 := by
  rw [pow_two_pow_succ, u39]; decide
private theorem u41 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 41 = 356778034244945469788419 := by
  rw [pow_two_pow_succ, u40]; decide
private theorem u42 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 42 = 259481065977581988771569 := by
  rw [pow_two_pow_succ, u41]; decide
private theorem u43 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 43 = 383741306690399955847930 := by
  rw [pow_two_pow_succ, u42]; decide
private theorem u44 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 44 = 290910559519063655783527 := by
  rw [pow_two_pow_succ, u43]; decide
private theorem u45 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 45 = 122804904151829285739829 := by
  rw [pow_two_pow_succ, u44]; decide
private theorem u46 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 46 = 415965487294324934941361 := by
  rw [pow_two_pow_succ, u45]; decide
private theorem u47 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 47 = 708984548382720203191980 := by
  rw [pow_two_pow_succ, u46]; decide
private theorem u48 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 48 = 179652784370398224320288 := by
  rw [pow_two_pow_succ, u47]; decide
private theorem u49 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 49 = 103453703927407656706626 := by
  rw [pow_two_pow_succ, u48]; decide
private theorem u50 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 50 = 993044355366015610594587 := by
  rw [pow_two_pow_succ, u49]; decide
private theorem u51 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 51 = 34904827283845339629219 := by
  rw [pow_two_pow_succ, u50]; decide
private theorem u52 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 52 = 978610721712035418941964 := by
  rw [pow_two_pow_succ, u51]; decide
private theorem u53 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 53 = 504144464295429059554113 := by
  rw [pow_two_pow_succ, u52]; decide
private theorem u54 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 54 = 377250996997219878328972 := by
  rw [pow_two_pow_succ, u53]; decide
private theorem u55 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 55 = 1155354439432236641395219 := by
  rw [pow_two_pow_succ, u54]; decide
private theorem u56 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 56 = 950409437763911233710235 := by
  rw [pow_two_pow_succ, u55]; decide
private theorem u57 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 57 = 643068962707287091929429 := by
  rw [pow_two_pow_succ, u56]; decide
private theorem u58 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 58 = 877247483790092304231457 := by
  rw [pow_two_pow_succ, u57]; decide
private theorem u59 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 59 = 350966889535864008599609 := by
  rw [pow_two_pow_succ, u58]; decide
private theorem u60 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 60 = 356315263103744277375543 := by
  rw [pow_two_pow_succ, u59]; decide
private theorem u61 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 61 = 569899337111144785138143 := by
  rw [pow_two_pow_succ, u60]; decide
private theorem u62 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 62 = 333399406091601700348918 := by
  rw [pow_two_pow_succ, u61]; decide
private theorem u63 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 63 = 1209755923097946104528896 := by
  rw [pow_two_pow_succ, u62]; decide
private theorem u64 : (698383666586983511969729 : ZMod P) ^ (2:ℕ) ^ 64 = 1 := by
  rw [pow_two_pow_succ, u63]; decide

/-! ### The Lucas certificate -/

private theorem cert_main : (3 : ZMod P) ^ (P - 1) = 1 := by
  rw [show P - 1 = 65581 * 2 ^ 64 from by norm_num, pow_mul, hx, u64]

private theorem cert_q2 : (3 : ZMod P) ^ ((P - 1) / 2) ≠ 1 := by
  rw [show (P - 1) / 2 = 65581 * 2 ^ 63 from by norm_num, pow_mul, hx, u63]
  decide

private theorem cert_qh : (3 : ZMod P) ^ ((P - 1) / 65581) ≠ 1 := by
  rw [show (P - 1) / 65581 = 2 ^ 64 from by norm_num, t64]
  decide

/-- **`P` is prime** — Lucas certificate with witness `3`, cofactors `{2, 65581}`. -/
theorem prime_P : Nat.Prime P := by
  refine lucas_primality P 3 cert_main ?_
  intro q hq hdvd
  rw [show P - 1 = 65581 * 2 ^ 64 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · have hq65581 : q = 65581 :=
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
    subst hq65581
    exact cert_qh
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst hq2
    exact cert_q2

local instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩

/-! ### The order-32 element `g = 3^((P−1)/32) = u_59` -/

private theorem g_def : (3 : ZMod P) ^ ((P - 1) / 32) = 350966889535864008599609 := by
  rw [show (P - 1) / 32 = 65581 * 2 ^ 59 from by norm_num, pow_mul, hx, u59]

theorem orderOf_gP : orderOf (350966889535864008599609 : ZMod P) = 32 := by
  have h4 : ¬ (350966889535864008599609 : ZMod P) ^ (2:ℕ) ^ 4 = 1 := by decide
  have h8 : (350966889535864008599609 : ZMod P) ^ (2:ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (350966889535864008599609 : ZMod P)) h4 h8
  norm_num at h
  exact h


/-! ### The four μ = 5 rungs: `δ* = 1 − r/32` for `r = 7, 8, 9, 10` -/

private theorem choose_32_7 : (32 : ℕ).choose 7 = 3365856 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_16_7 : (16 : ℕ).choose 7 = 11440 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

private theorem choose_32_8 : (32 : ℕ).choose 8 = 10518300 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_16_8 : (16 : ℕ).choose 8 = 12870 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

private theorem choose_32_9 : (32 : ℕ).choose 9 = 28048800 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_16_9 : (16 : ℕ).choose 9 = 11440 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

private theorem choose_32_10 : (32 : ℕ).choose 10 = 64512240 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_16_10 : (16 : ℕ).choose 10 = 8008 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- **`δ* = 25/32` exactly** for the dimension-6 (rate `6/32`) code on the
32-point smooth domain `⟨g⟩ ⊆ F_P^×` at `ε* = 480836/P` — beyond Johnson
(`7² = 49 < 192 = 6·32`), below capacity. -/
theorem deltaStar_pin_P_dimSix :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode (350966889535864008599609 : ZMod P) 32 5)
        ((480836 : ℝ≥0∞) / (P : ℝ≥0∞))
      = 25 / 32 := by
  haveI : NeZero (32 : ℕ) := ⟨by norm_num⟩
  have hc : ((32 : ℕ).choose 7 / 7 : ℕ) = 480836 := by
    rw [choose_32_7]
  have hp0 : (P : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  have hpt : (P : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top P
  have h := KKH26CeilingMarch.kkh26_march_deltaStar_pin (p := P) (μ := 5) (r := 7)
    (g := (350966889535864008599609 : ZMod P)) (n := 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact orderOf_gP) (by norm_num)
    (((480836 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞)) ?hlo ?hhi
  case hlo =>
    exact le_of_eq (by rw [hc])
  case hhi =>
    refine ENNReal.div_lt_div_right hp0 hpt ?_
    have hb : (480836 : ℕ) < (2 ^ 7 * (2 ^ (5 - 1)).choose 7 : ℕ) := by
      show (480836 : ℕ) < 2 ^ 7 * (16 : ℕ).choose 7
      rw [choose_16_7]
      norm_num
    exact_mod_cast hb
  have e1 : ((480836 : ℕ) : ℝ≥0∞) = (480836 : ℝ≥0∞) := by norm_num
  have e2 : (((7 : ℕ)) : ℝ≥0) = (7 : ℝ≥0) := by norm_num
  rw [e1, e2] at h
  rw [h]
  have hd : (7 : ℝ≥0) / ((2 : ℝ≥0) ^ 5) = 7 / 32 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- **`δ* = 3/4` exactly** for the dimension-7 (rate `7/32`) code on the
32-point smooth domain `⟨g⟩ ⊆ F_P^×` at `ε* = 1314787/P` — beyond Johnson
(`8² = 64 < 224 = 7·32`), below capacity. -/
theorem deltaStar_pin_P_dimSeven :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode (350966889535864008599609 : ZMod P) 32 6)
        ((1314787 : ℝ≥0∞) / (P : ℝ≥0∞))
      = 3 / 4 := by
  haveI : NeZero (32 : ℕ) := ⟨by norm_num⟩
  have hc : ((32 : ℕ).choose 8 / 8 : ℕ) = 1314787 := by
    rw [choose_32_8]
  have hp0 : (P : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  have hpt : (P : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top P
  have h := KKH26CeilingMarch.kkh26_march_deltaStar_pin (p := P) (μ := 5) (r := 8)
    (g := (350966889535864008599609 : ZMod P)) (n := 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact orderOf_gP) (by norm_num)
    (((1314787 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞)) ?hlo ?hhi
  case hlo =>
    exact le_of_eq (by rw [hc])
  case hhi =>
    refine ENNReal.div_lt_div_right hp0 hpt ?_
    have hb : (1314787 : ℕ) < (2 ^ 8 * (2 ^ (5 - 1)).choose 8 : ℕ) := by
      show (1314787 : ℕ) < 2 ^ 8 * (16 : ℕ).choose 8
      rw [choose_16_8]
      norm_num
    exact_mod_cast hb
  have e1 : ((1314787 : ℕ) : ℝ≥0∞) = (1314787 : ℝ≥0∞) := by norm_num
  have e2 : (((8 : ℕ)) : ℝ≥0) = (8 : ℝ≥0) := by norm_num
  rw [e1, e2] at h
  rw [h]
  have hd : (8 : ℝ≥0) / ((2 : ℝ≥0) ^ 5) = 8 / 32 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- **`δ* = 23/32` exactly** for the dimension-8 (rate `8/32`) code on the
32-point smooth domain `⟨g⟩ ⊆ F_P^×` at `ε* = 3116533/P` — beyond Johnson
(`9² = 81 < 256 = 8·32`), below capacity. -/
theorem deltaStar_pin_P_dimEight :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode (350966889535864008599609 : ZMod P) 32 7)
        ((3116533 : ℝ≥0∞) / (P : ℝ≥0∞))
      = 23 / 32 := by
  haveI : NeZero (32 : ℕ) := ⟨by norm_num⟩
  have hc : ((32 : ℕ).choose 9 / 9 : ℕ) = 3116533 := by
    rw [choose_32_9]
  have hp0 : (P : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  have hpt : (P : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top P
  have h := KKH26CeilingMarch.kkh26_march_deltaStar_pin (p := P) (μ := 5) (r := 9)
    (g := (350966889535864008599609 : ZMod P)) (n := 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact orderOf_gP) (by norm_num)
    (((3116533 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞)) ?hlo ?hhi
  case hlo =>
    exact le_of_eq (by rw [hc])
  case hhi =>
    refine ENNReal.div_lt_div_right hp0 hpt ?_
    have hb : (3116533 : ℕ) < (2 ^ 9 * (2 ^ (5 - 1)).choose 9 : ℕ) := by
      show (3116533 : ℕ) < 2 ^ 9 * (16 : ℕ).choose 9
      rw [choose_16_9]
      norm_num
    exact_mod_cast hb
  have e1 : ((3116533 : ℕ) : ℝ≥0∞) = (3116533 : ℝ≥0∞) := by norm_num
  have e2 : (((9 : ℕ)) : ℝ≥0) = (9 : ℝ≥0) := by norm_num
  rw [e1, e2] at h
  rw [h]
  have hd : (9 : ℝ≥0) / ((2 : ℝ≥0) ^ 5) = 9 / 32 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- **`δ* = 11/16` exactly** for the dimension-9 (rate `9/32`) code on the
32-point smooth domain `⟨g⟩ ⊆ F_P^×` at `ε* = 6451224/P` — beyond Johnson
(`10² = 100 < 288 = 9·32`), below capacity. -/
theorem deltaStar_pin_P_dimNine :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode (350966889535864008599609 : ZMod P) 32 8)
        ((6451224 : ℝ≥0∞) / (P : ℝ≥0∞))
      = 11 / 16 := by
  haveI : NeZero (32 : ℕ) := ⟨by norm_num⟩
  have hc : ((32 : ℕ).choose 10 / 10 : ℕ) = 6451224 := by
    rw [choose_32_10]
  have hp0 : (P : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  have hpt : (P : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top P
  have h := KKH26CeilingMarch.kkh26_march_deltaStar_pin (p := P) (μ := 5) (r := 10)
    (g := (350966889535864008599609 : ZMod P)) (n := 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact orderOf_gP) (by norm_num)
    (((6451224 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞)) ?hlo ?hhi
  case hlo =>
    exact le_of_eq (by rw [hc])
  case hhi =>
    refine ENNReal.div_lt_div_right hp0 hpt ?_
    have hb : (6451224 : ℕ) < (2 ^ 10 * (2 ^ (5 - 1)).choose 10 : ℕ) := by
      show (6451224 : ℕ) < 2 ^ 10 * (16 : ℕ).choose 10
      rw [choose_16_10]
      norm_num
    exact_mod_cast hb
  have e1 : ((6451224 : ℕ) : ℝ≥0∞) = (6451224 : ℝ≥0∞) := by norm_num
  have e2 : (((10 : ℕ)) : ℝ≥0) = (10 : ℝ≥0) := by norm_num
  rw [e1, e2] at h
  rw [h]
  have hd : (10 : ℝ≥0) / ((2 : ℝ≥0) ^ 5) = 10 / 32 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num


end ArkLib.ProximityGap.CertifiedRungPrime

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.CertifiedRungPrime.prime_P
#print axioms ArkLib.ProximityGap.CertifiedRungPrime.orderOf_gP
#print axioms ArkLib.ProximityGap.CertifiedRungPrime.deltaStar_pin_P_dimSix
#print axioms ArkLib.ProximityGap.CertifiedRungPrime.deltaStar_pin_P_dimSeven
#print axioms ArkLib.ProximityGap.CertifiedRungPrime.deltaStar_pin_P_dimEight
#print axioms ArkLib.ProximityGap.CertifiedRungPrime.deltaStar_pin_P_dimNine
