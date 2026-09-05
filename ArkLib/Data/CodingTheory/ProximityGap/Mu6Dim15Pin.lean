/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Mu6ConditionalPin

/-!
# The μ = 6 dimension-15 (rate 15/64) literal-budget pin — the top of the ladder

The μ = 6 literal-budget family already has three unconditional rungs:
`Mu6ConditionalPin.lean` lands `r = 5` (dimension 4, rate `1/16`), `Mu6Dim8Pin.lean`
lands `r = 9` (dimension 8, rate `1/8`), and `Mu6DeepRung.lean` lands `r = 13`
(dimension 12, rate `3/16`) — the deepest rung and highest rate to date.

This file lands `r = 16`, which is the **largest** rung the μ = 6 literal budget band
admits at all: `Mu6LiteralBands.mu6_band_closed_of_ge_17` shows the band is empty for
every `r ≥ 17`, so `r = 16` terminates the ladder on the 64-point smooth domain.

The band edges are

* low  `⌊C(64,16)/16⌋ = 30532933567473`
* high `2^16·C(32,16)  = 39392404439040`

a window only `log₂(hi/lo) ≈ 0.368` bits wide, against `≈ 2.23` bits at `r = 9` and
`≈ 1.49` bits at `r = 13`.  That is why the Proth coefficient here has to be found by
search rather than written down.  We use the 173-bit Proth prime

`Q = 30532933579843·2^128 + 1`

whose Proth coefficient `K = 30532933579843` sits inside the band.  `K` is itself prime,
but at ~3·10¹³ it is far beyond what `norm_num` can certify by trial division, so this
file carries a **two-level Lucas certificate**: an inner `lucas_primality` run for `K`
(base 2, using `K - 1 = 2·3⁴·113·2857·583801`) feeding the outer run for `Q` (base 3).

The bad side is again free: `collisionResultant_not_dvd_of_cyclotomicLandauSqBound` asks
only for `landauSqEnvelope (2^(μ-1)) < p^2`, and `landauSqEnvelope (2^5) = 2^255` does not
mention `r`.

The resulting pin is at **rate 15/64 ≈ 0.234** with `δ* = 48/64 = 3/4`, which is

* strictly beyond the Johnson bound `1 - √(15/64) ≈ 0.5159`, and
* strictly below capacity `1 - 15/64 = 49/64 ≈ 0.7656`.

Two caveats on how to read that.  First, the `1/64` gap to capacity is *structural, not
sharp*: every rung of this family has `δ* = (64-r)/64` against capacity `(65-r)/64`, so
`r = 5`, `9`, `13` and `16` all sit exactly `1/64` below capacity.  Nothing about `r = 16`
tightens that gap.  Second, `15/64` is the highest rate any rung of this family reaches
(it supersedes the `3/16` of `Mu6DeepRung.lean`), but it is **not** one of the Proximity
Prize rates — `1/2`, `1/4`, `1/8`, `1/16`.  It falls just short of `1/4`, and since
`mu6_band_closed_of_ge_17` closes every higher rung, no member of this construction
reaches `1/4` or `1/2` at μ = 6 *at all*.  What is new here is the exhibited witness at
the top rung, the *termination* of the ladder, and the certificate technique below.

## Main results

* `prime_K` — inner Lucas certificate for the Proth coefficient.
* `prime_Q` — outer Lucas certificate for the 173-bit Proth prime.
* `orderOf_gQ` — the order-64 generator certificate.
* `Q_mem_band_r16` — `Q` inhabits the (very narrow) `r = 16` literal-budget band.
* `deltaStar_pin_mu6_dim15` — the unconditional pin.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ProximityGap.StaircaseBandTheorem

namespace ArkLib.ProximityGap.Mu6Dim15Pin

/-- The Proth coefficient `K = 30532933579843`, itself prime and inside the `r = 16` band. -/
abbrev K : ℕ := 30532933579843

/-- The certified 173-bit Proth prime `Q = K·2^128 + 1`. -/
abbrev Q : ℕ := 10389818907588778884587886312609003368974655483281409

private theorem pow_two_pow_succ {M : Type*} [Monoid M] (a : M) (k : ℕ) :
    a ^ (2:ℕ) ^ (k + 1) = (a ^ (2:ℕ) ^ k) ^ 2 := by
  rw [← pow_mul, ← pow_succ]

/-! ## Inner Lucas certificate: the Proth coefficient `K` is prime

`K` is ~3·10¹³, well past `norm_num`'s trial-division reach, so it gets its own
`lucas_primality` run at base 2 over `K - 1 = 2·3⁴·113·2857·583801`. -/

private theorem s0 : (2 : ZMod K) ^ (2:ℕ) ^ 0 = 2 := by norm_num
private theorem s1 : (2 : ZMod K) ^ (2:ℕ) ^ 1 = 4 := by
  rw [pow_two_pow_succ, s0]; decide
private theorem s2 : (2 : ZMod K) ^ (2:ℕ) ^ 2 = 16 := by
  rw [pow_two_pow_succ, s1]; decide
private theorem s3 : (2 : ZMod K) ^ (2:ℕ) ^ 3 = 256 := by
  rw [pow_two_pow_succ, s2]; decide
private theorem s4 : (2 : ZMod K) ^ (2:ℕ) ^ 4 = 65536 := by
  rw [pow_two_pow_succ, s3]; decide
private theorem s5 : (2 : ZMod K) ^ (2:ℕ) ^ 5 = 4294967296 := by
  rw [pow_two_pow_succ, s4]; decide
private theorem s6 : (2 : ZMod K) ^ (2:ℕ) ^ 6 = 27987978764422 := by
  rw [pow_two_pow_succ, s5]; decide
private theorem s7 : (2 : ZMod K) ^ (2:ℕ) ^ 7 = 13946781751482 := by
  rw [pow_two_pow_succ, s6]; decide
private theorem s8 : (2 : ZMod K) ^ (2:ℕ) ^ 8 = 26983953746632 := by
  rw [pow_two_pow_succ, s7]; decide
private theorem s9 : (2 : ZMod K) ^ (2:ℕ) ^ 9 = 7272339251169 := by
  rw [pow_two_pow_succ, s8]; decide
private theorem s10 : (2 : ZMod K) ^ (2:ℕ) ^ 10 = 28435577587479 := by
  rw [pow_two_pow_succ, s9]; decide
private theorem s11 : (2 : ZMod K) ^ (2:ℕ) ^ 11 = 27771091140722 := by
  rw [pow_two_pow_succ, s10]; decide
private theorem s12 : (2 : ZMod K) ^ (2:ℕ) ^ 12 = 11296135949451 := by
  rw [pow_two_pow_succ, s11]; decide
private theorem s13 : (2 : ZMod K) ^ (2:ℕ) ^ 13 = 21109681860246 := by
  rw [pow_two_pow_succ, s12]; decide
private theorem s14 : (2 : ZMod K) ^ (2:ℕ) ^ 14 = 6895751017885 := by
  rw [pow_two_pow_succ, s13]; decide
private theorem s15 : (2 : ZMod K) ^ (2:ℕ) ^ 15 = 11134485987872 := by
  rw [pow_two_pow_succ, s14]; decide
private theorem s16 : (2 : ZMod K) ^ (2:ℕ) ^ 16 = 6731867939650 := by
  rw [pow_two_pow_succ, s15]; decide
private theorem s17 : (2 : ZMod K) ^ (2:ℕ) ^ 17 = 28247790341903 := by
  rw [pow_two_pow_succ, s16]; decide
private theorem s18 : (2 : ZMod K) ^ (2:ℕ) ^ 18 = 3052823586451 := by
  rw [pow_two_pow_succ, s17]; decide
private theorem s19 : (2 : ZMod K) ^ (2:ℕ) ^ 19 = 16759942784284 := by
  rw [pow_two_pow_succ, s18]; decide
private theorem s20 : (2 : ZMod K) ^ (2:ℕ) ^ 20 = 25291842718653 := by
  rw [pow_two_pow_succ, s19]; decide
private theorem s21 : (2 : ZMod K) ^ (2:ℕ) ^ 21 = 27985939236035 := by
  rw [pow_two_pow_succ, s20]; decide
private theorem s22 : (2 : ZMod K) ^ (2:ℕ) ^ 22 = 18549844877024 := by
  rw [pow_two_pow_succ, s21]; decide
private theorem s23 : (2 : ZMod K) ^ (2:ℕ) ^ 23 = 6362152006282 := by
  rw [pow_two_pow_succ, s22]; decide
private theorem s24 : (2 : ZMod K) ^ (2:ℕ) ^ 24 = 3682296561509 := by
  rw [pow_two_pow_succ, s23]; decide
private theorem s25 : (2 : ZMod K) ^ (2:ℕ) ^ 25 = 22690334828879 := by
  rw [pow_two_pow_succ, s24]; decide
private theorem s26 : (2 : ZMod K) ^ (2:ℕ) ^ 26 = 22338235561617 := by
  rw [pow_two_pow_succ, s25]; decide
private theorem s27 : (2 : ZMod K) ^ (2:ℕ) ^ 27 = 14849676803200 := by
  rw [pow_two_pow_succ, s26]; decide
private theorem s28 : (2 : ZMod K) ^ (2:ℕ) ^ 28 = 19168596351619 := by
  rw [pow_two_pow_succ, s27]; decide
private theorem s29 : (2 : ZMod K) ^ (2:ℕ) ^ 29 = 27305692680068 := by
  rw [pow_two_pow_succ, s28]; decide
private theorem s30 : (2 : ZMod K) ^ (2:ℕ) ^ 30 = 9835563118384 := by
  rw [pow_two_pow_succ, s29]; decide
private theorem s31 : (2 : ZMod K) ^ (2:ℕ) ^ 31 = 16952870627791 := by
  rw [pow_two_pow_succ, s30]; decide
private theorem s32 : (2 : ZMod K) ^ (2:ℕ) ^ 32 = 19302427153191 := by
  rw [pow_two_pow_succ, s31]; decide
private theorem s33 : (2 : ZMod K) ^ (2:ℕ) ^ 33 = 3625066784117 := by
  rw [pow_two_pow_succ, s32]; decide
private theorem s34 : (2 : ZMod K) ^ (2:ℕ) ^ 34 = 7275197425235 := by
  rw [pow_two_pow_succ, s33]; decide
private theorem s35 : (2 : ZMod K) ^ (2:ℕ) ^ 35 = 1014808331127 := by
  rw [pow_two_pow_succ, s34]; decide
private theorem s36 : (2 : ZMod K) ^ (2:ℕ) ^ 36 = 19593961720959 := by
  rw [pow_two_pow_succ, s35]; decide
private theorem s37 : (2 : ZMod K) ^ (2:ℕ) ^ 37 = 4992544812514 := by
  rw [pow_two_pow_succ, s36]; decide
private theorem s38 : (2 : ZMod K) ^ (2:ℕ) ^ 38 = 14546976885580 := by
  rw [pow_two_pow_succ, s37]; decide
private theorem s39 : (2 : ZMod K) ^ (2:ℕ) ^ 39 = 2706803648223 := by
  rw [pow_two_pow_succ, s38]; decide
private theorem s40 : (2 : ZMod K) ^ (2:ℕ) ^ 40 = 130203078881 := by
  rw [pow_two_pow_succ, s39]; decide
private theorem s41 : (2 : ZMod K) ^ (2:ℕ) ^ 41 = 2292948013169 := by
  rw [pow_two_pow_succ, s40]; decide
private theorem s42 : (2 : ZMod K) ^ (2:ℕ) ^ 42 = 947314246469 := by
  rw [pow_two_pow_succ, s41]; decide
private theorem s43 : (2 : ZMod K) ^ (2:ℕ) ^ 43 = 14698356899315 := by
  rw [pow_two_pow_succ, s42]; decide
private theorem s44 : (2 : ZMod K) ^ (2:ℕ) ^ 44 = 24229976946931 := by
  rw [pow_two_pow_succ, s43]; decide
private theorem s45 : (2 : ZMod K) ^ (2:ℕ) ^ 45 = 12183956993990 := by
  rw [pow_two_pow_succ, s44]; decide

private theorem kmain :
    (2 : ZMod K) ^ (30532933579842:ℕ) = 1 := by
  rw [show (30532933579842:ℕ) = 2^44 + 2^43 + 2^41 + 2^40 + 2^39 + 2^38 + 2^34 + 2^32 + 2^23 +
    2^21 + 2^19 + 2^15 + 2^14 + 2^13 + 2^12 + 2^10 + 2^6 + 2^1 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    s44, s43, s41, s40, s39, s38, s34, s32, s23, s21, s19, s15, s14, s13, s12, s10, s6, s1]
  decide
private theorem kq2 :
    (2 : ZMod K) ^ (15266466789921:ℕ) ≠ 1 := by
  rw [show (15266466789921:ℕ) = 2^43 + 2^42 + 2^40 + 2^39 + 2^38 + 2^37 + 2^33 + 2^31 + 2^22 +
    2^20 + 2^18 + 2^14 + 2^13 + 2^12 + 2^11 + 2^9 + 2^5 + 2^0 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    s43, s42, s40, s39, s38, s37, s33, s31, s22, s20, s18, s14, s13, s12, s11, s9, s5, s0]
  decide
private theorem kq3 :
    (2 : ZMod K) ^ (10177644526614:ℕ) ≠ 1 := by
  rw [show (10177644526614:ℕ) = 2^43 + 2^40 + 2^38 + 2^32 + 2^31 + 2^29 + 2^27 + 2^25 + 2^23 +
    2^22 + 2^21 + 2^17 + 2^15 + 2^14 + 2^13 + 2^12 + 2^11 + 2^10 + 2^4 + 2^2 + 2^1 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    s43, s40, s38, s32, s31, s29, s27, s25, s23, s22, s21, s17, s15, s14, s13, s12, s11, s10, s4,
      s2, s1]
  decide
private theorem kq113 :
    (2 : ZMod K) ^ (270202952034:ℕ) ≠ 1 := by
  rw [show (270202952034:ℕ) = 2^37 + 2^36 + 2^35 + 2^34 + 2^33 + 2^31 + 2^30 + 2^29 + 2^27 + 2^24 +
    2^22 + 2^20 + 2^19 + 2^16 + 2^15 + 2^14 + 2^12 + 2^11 + 2^8 + 2^6 + 2^5 + 2^1 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add,
    s37, s36, s35, s34, s33, s31, s30, s29, s27, s24, s22, s20, s19, s16, s15, s14, s12, s11, s8,
      s6, s5, s1]
  decide
private theorem kq2857 :
    (2 : ZMod K) ^ (10687061106:ℕ) ≠ 1 := by
  rw [show (10687061106:ℕ) = 2^33 + 2^30 + 2^29 + 2^28 + 2^27 + 2^26 + 2^23 + 2^22 + 2^21 + 2^20 +
    2^19 + 2^18 + 2^17 + 2^16 + 2^15 + 2^12 + 2^11 + 2^10 + 2^6 + 2^5 + 2^4 + 2^1 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add,
    s33, s30, s29, s28, s27, s26, s23, s22, s21, s20, s19, s18, s17, s16, s15, s12, s11, s10, s6,
      s5, s4, s1]
  decide
private theorem kq583801 :
    (2 : ZMod K) ^ (52300242:ℕ) ≠ 1 := by
  rw [show (52300242:ℕ) = 2^25 + 2^24 + 2^20 + 2^19 + 2^18 + 2^17 + 2^11 + 2^8 + 2^7 + 2^6 + 2^4 +
    2^1 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add,
    s25, s24, s20, s19, s18, s17, s11, s8, s7, s6, s4, s1]
  decide

/-- **The Proth coefficient is prime.**  Inner Lucas certificate, base 2. -/
theorem prime_K : Nat.Prime K := by
  refine lucas_primality K 2 kmain ?_
  intro q hq hdvd
  rw [show K - 1 = 2 * 3 ^ 4 * 113 * 2857 * 583801 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
          subst hq2; exact kq2
        · have hq3 : q = 3 :=
            (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
          subst hq3; exact kq3
      · have hq113 : q = 113 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hq113; exact kq113
    · have hq2857 : q = 2857 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hq2857; exact kq2857
  · have hq583801 : q = 583801 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
    subst hq583801; exact kq583801

/-! ## Repeated-squaring chain for the base `3` modulo `Q` -/

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
    (3 : ZMod Q) ^ (2:ℕ) ^ 7 = 7135908772808808607753155426214763296065610433368551 := by
  rw [pow_two_pow_succ, t6]; decide
private theorem t8 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 8 = 8483623130443115624727035297855033109421383733376798 := by
  rw [pow_two_pow_succ, t7]; decide
private theorem t9 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 9 = 4255603591056289063523143564455444027720602004468967 := by
  rw [pow_two_pow_succ, t8]; decide
private theorem t10 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 10 = 2659451539909881219999492433869824774435188988249143 := by
  rw [pow_two_pow_succ, t9]; decide
private theorem t11 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 11 = 4910834479413726555053565246133628083492770493200063 := by
  rw [pow_two_pow_succ, t10]; decide
private theorem t12 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 12 = 8314370002131809671902340980604411318684689395951983 := by
  rw [pow_two_pow_succ, t11]; decide
private theorem t13 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 13 = 3351106395871558684108699393769622292603804015159677 := by
  rw [pow_two_pow_succ, t12]; decide
private theorem t14 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 14 = 1304350954457182811792957283273366932548034714960629 := by
  rw [pow_two_pow_succ, t13]; decide
private theorem t15 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 15 = 1875653311607332984213223523053940319076202844997477 := by
  rw [pow_two_pow_succ, t14]; decide
private theorem t16 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 16 = 4027323180122494001240721354963426128072156303490992 := by
  rw [pow_two_pow_succ, t15]; decide
private theorem t17 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 17 = 9551304642184891789309556556589054405039813660120659 := by
  rw [pow_two_pow_succ, t16]; decide
private theorem t18 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 18 = 133279879213563088857117773190412651672187662949668 := by
  rw [pow_two_pow_succ, t17]; decide
private theorem t19 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 19 = 3285557392008280399545840425574550341958138085628846 := by
  rw [pow_two_pow_succ, t18]; decide
private theorem t20 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 20 = 1587963219307957519435259925351811870362654978301132 := by
  rw [pow_two_pow_succ, t19]; decide
private theorem t21 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 21 = 2073182803952395163481217891535267393177718476756507 := by
  rw [pow_two_pow_succ, t20]; decide
private theorem t22 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 22 = 8829944851377808580966148122296769163897546845454386 := by
  rw [pow_two_pow_succ, t21]; decide
private theorem t23 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 23 = 1327829009489588497274871120558714490502079424524577 := by
  rw [pow_two_pow_succ, t22]; decide
private theorem t24 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 24 = 1739344356424056071353381382653723476533449398833141 := by
  rw [pow_two_pow_succ, t23]; decide
private theorem t25 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 25 = 8286421088878585105195534580818259518940638246992113 := by
  rw [pow_two_pow_succ, t24]; decide
private theorem t26 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 26 = 7406456808089787814046254307895265077093635311772539 := by
  rw [pow_two_pow_succ, t25]; decide
private theorem t27 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 27 = 2330714382282326058471474735501583767807055398927352 := by
  rw [pow_two_pow_succ, t26]; decide
private theorem t28 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 28 = 8787933132447957566351355758427633977377977313945184 := by
  rw [pow_two_pow_succ, t27]; decide
private theorem t29 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 29 = 5349673305205681392990309750939082800215832388980801 := by
  rw [pow_two_pow_succ, t28]; decide
private theorem t30 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 30 = 6710955906031546834060346245493525078838460329749723 := by
  rw [pow_two_pow_succ, t29]; decide
private theorem t31 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 31 = 5002696425630129822903401973133963624736905440546591 := by
  rw [pow_two_pow_succ, t30]; decide
private theorem t32 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 32 = 10360795531226887646238892274475443102789621209469041 := by
  rw [pow_two_pow_succ, t31]; decide
private theorem t33 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 33 = 8925862323572389411620611847081927193928633563110683 := by
  rw [pow_two_pow_succ, t32]; decide
private theorem t34 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 34 = 3108219084857333442291973613979573728656358282230069 := by
  rw [pow_two_pow_succ, t33]; decide
private theorem t35 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 35 = 4754134115325553326734734098743832824363572585633194 := by
  rw [pow_two_pow_succ, t34]; decide
private theorem t36 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 36 = 4623053729220060011577272093591237623991629082128710 := by
  rw [pow_two_pow_succ, t35]; decide
private theorem t37 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 37 = 6902225548962459306781641525918513088416116726998368 := by
  rw [pow_two_pow_succ, t36]; decide
private theorem t38 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 38 = 1447907077457758668694390080678842827088946640836671 := by
  rw [pow_two_pow_succ, t37]; decide
private theorem t39 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 39 = 6852118649234719032916892068178392981008386274802154 := by
  rw [pow_two_pow_succ, t38]; decide
private theorem t40 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 40 = 2604864149988669019668329212810650035167913861527128 := by
  rw [pow_two_pow_succ, t39]; decide
private theorem t41 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 41 = 2861422288720091699651551276128539218889535120815244 := by
  rw [pow_two_pow_succ, t40]; decide
private theorem t42 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 42 = 2477778886327906389950380339983255541977632638297365 := by
  rw [pow_two_pow_succ, t41]; decide
private theorem t43 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 43 = 2013902667638921722403623288065616988359721253767374 := by
  rw [pow_two_pow_succ, t42]; decide
private theorem t44 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 44 = 6743585745156154653736270085246182436160963584279377 := by
  rw [pow_two_pow_succ, t43]; decide
private theorem t45 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 45 = 3789174705609284285902492808744063428841724928749356 := by
  rw [pow_two_pow_succ, t44]; decide
private theorem t46 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 46 = 8080483383649562197506906382395972981962967786285203 := by
  rw [pow_two_pow_succ, t45]; decide
private theorem t47 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 47 = 150170959100674842104729589418489077693443575298350 := by
  rw [pow_two_pow_succ, t46]; decide
private theorem t48 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 48 = 9786415627035147727449763160196347315459199465347116 := by
  rw [pow_two_pow_succ, t47]; decide
private theorem t49 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 49 = 10242155436244653116627956174911644513814632919845193 := by
  rw [pow_two_pow_succ, t48]; decide
private theorem t50 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 50 = 1187866811762251255197660133073333021601280683075110 := by
  rw [pow_two_pow_succ, t49]; decide
private theorem t51 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 51 = 6900784429521707999721607137923790990488832029066678 := by
  rw [pow_two_pow_succ, t50]; decide
private theorem t52 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 52 = 4397257015671334206961288542550049742200512327840004 := by
  rw [pow_two_pow_succ, t51]; decide
private theorem t53 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 53 = 4972090722654226043555417032808434791566812210042612 := by
  rw [pow_two_pow_succ, t52]; decide
private theorem t54 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 54 = 1948436578706918058394337349645550668792531579900013 := by
  rw [pow_two_pow_succ, t53]; decide
private theorem t55 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 55 = 3752552995694521870208248665602580910955884256087553 := by
  rw [pow_two_pow_succ, t54]; decide
private theorem t56 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 56 = 5206237495591365241517029618393415889437404284801228 := by
  rw [pow_two_pow_succ, t55]; decide
private theorem t57 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 57 = 3462549276428436338418836937051257049998073817382808 := by
  rw [pow_two_pow_succ, t56]; decide
private theorem t58 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 58 = 5133625119331941413482463092464162928263791903640341 := by
  rw [pow_two_pow_succ, t57]; decide
private theorem t59 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 59 = 289477390413779388257986362226098950034992383331981 := by
  rw [pow_two_pow_succ, t58]; decide
private theorem t60 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 60 = 2391410150177026916283801194537389365029126990411079 := by
  rw [pow_two_pow_succ, t59]; decide
private theorem t61 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 61 = 2337479743604384195229242723755683330380989153833789 := by
  rw [pow_two_pow_succ, t60]; decide
private theorem t62 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 62 = 8033044969541099137638043884819495534349291328990759 := by
  rw [pow_two_pow_succ, t61]; decide
private theorem t63 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 63 = 6830611911841906871580835465881682896285078916370999 := by
  rw [pow_two_pow_succ, t62]; decide
private theorem t64 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 64 = 5910842604841860239773311856985889636534370274255872 := by
  rw [pow_two_pow_succ, t63]; decide
private theorem t65 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 65 = 6840919731378860944578650239094233671452306728227547 := by
  rw [pow_two_pow_succ, t64]; decide
private theorem t66 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 66 = 10024975382341103186717115741939427034522060357180464 := by
  rw [pow_two_pow_succ, t65]; decide
private theorem t67 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 67 = 3685203094047817413705211402480640458969114569229560 := by
  rw [pow_two_pow_succ, t66]; decide
private theorem t68 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 68 = 8027364323632599955208563632130306031732766640521996 := by
  rw [pow_two_pow_succ, t67]; decide
private theorem t69 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 69 = 2996141647856102559800300470419917391108480160437621 := by
  rw [pow_two_pow_succ, t68]; decide
private theorem t70 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 70 = 7505731656410116775198401885955471434098461276265413 := by
  rw [pow_two_pow_succ, t69]; decide
private theorem t71 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 71 = 8327891292826107111164112025631311833212188778645424 := by
  rw [pow_two_pow_succ, t70]; decide
private theorem t72 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 72 = 6054778131987212404665461072443815831534420519532843 := by
  rw [pow_two_pow_succ, t71]; decide
private theorem t73 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 73 = 9343095317428857985663744586464209586896652812600047 := by
  rw [pow_two_pow_succ, t72]; decide
private theorem t74 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 74 = 3039852038798714955660253316424239186568561472545553 := by
  rw [pow_two_pow_succ, t73]; decide
private theorem t75 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 75 = 7060278260261900248893923468652437172317065021164543 := by
  rw [pow_two_pow_succ, t74]; decide
private theorem t76 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 76 = 3118877570895687443341557915118517565909418736942545 := by
  rw [pow_two_pow_succ, t75]; decide
private theorem t77 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 77 = 8696925271011284502875182563896181630947501904390096 := by
  rw [pow_two_pow_succ, t76]; decide
private theorem t78 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 78 = 3188331875924216215333324615789093665904957718395200 := by
  rw [pow_two_pow_succ, t77]; decide
private theorem t79 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 79 = 5426833051269684064684269113916642980096249873619346 := by
  rw [pow_two_pow_succ, t78]; decide
private theorem t80 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 80 = 2955106304666984795268810913609055826066159679398108 := by
  rw [pow_two_pow_succ, t79]; decide
private theorem t81 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 81 = 8616619726723936861762112930615546625893682657290822 := by
  rw [pow_two_pow_succ, t80]; decide
private theorem t82 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 82 = 9550414920887055780427828535201276679577052979673232 := by
  rw [pow_two_pow_succ, t81]; decide
private theorem t83 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 83 = 6997545548056855412070229704413449178331874177768222 := by
  rw [pow_two_pow_succ, t82]; decide
private theorem t84 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 84 = 5807938990437763310855781678332718017670936690755799 := by
  rw [pow_two_pow_succ, t83]; decide
private theorem t85 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 85 = 6007717360688235951903593013219254303021996355174607 := by
  rw [pow_two_pow_succ, t84]; decide
private theorem t86 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 86 = 946653223029578403511278345026822672107365975032451 := by
  rw [pow_two_pow_succ, t85]; decide
private theorem t87 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 87 = 1933737147801421224391837840597926702872655106546476 := by
  rw [pow_two_pow_succ, t86]; decide
private theorem t88 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 88 = 1128117264597152306127668398977096357218272741345697 := by
  rw [pow_two_pow_succ, t87]; decide
private theorem t89 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 89 = 9074094702281367617960238837538815119763075663822536 := by
  rw [pow_two_pow_succ, t88]; decide
private theorem t90 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 90 = 9689526438593448031435797475152506950784035557210065 := by
  rw [pow_two_pow_succ, t89]; decide
private theorem t91 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 91 = 8747944980808845102737313935052141715668299153157406 := by
  rw [pow_two_pow_succ, t90]; decide
private theorem t92 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 92 = 2754570358584938253320399446134104059213665313728703 := by
  rw [pow_two_pow_succ, t91]; decide
private theorem t93 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 93 = 8225836623967594717642132098721652130767044498227612 := by
  rw [pow_two_pow_succ, t92]; decide
private theorem t94 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 94 = 6219325252859014554465168258583217980925272074143915 := by
  rw [pow_two_pow_succ, t93]; decide
private theorem t95 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 95 = 1393172216292327244685378063655013840219033351744326 := by
  rw [pow_two_pow_succ, t94]; decide
private theorem t96 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 96 = 2878667520237010743255742169659019273865266979897435 := by
  rw [pow_two_pow_succ, t95]; decide
private theorem t97 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 97 = 961592792928422495811301850441091536624188833485854 := by
  rw [pow_two_pow_succ, t96]; decide
private theorem t98 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 98 = 4252249103519480309187625525652662465441781980742961 := by
  rw [pow_two_pow_succ, t97]; decide
private theorem t99 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 99 = 5361583143582282136559594328670985660322066105031509 := by
  rw [pow_two_pow_succ, t98]; decide
private theorem t100 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 100 = 8378714260543967780070807056545932217326658359043833 := by
  rw [pow_two_pow_succ, t99]; decide
private theorem t101 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 101 = 3689123561808694226379320676031726035681212741508212 := by
  rw [pow_two_pow_succ, t100]; decide
private theorem t102 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 102 = 10368660949187180367473223454426044234384548168854690 := by
  rw [pow_two_pow_succ, t101]; decide
private theorem t103 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 103 = 2716011820542355960062422480635931889095680396851473 := by
  rw [pow_two_pow_succ, t102]; decide
private theorem t104 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 104 = 4482999723454885190429377828640886371104353600558076 := by
  rw [pow_two_pow_succ, t103]; decide
private theorem t105 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 105 = 9983522855436361512578743230400399414139452652997218 := by
  rw [pow_two_pow_succ, t104]; decide
private theorem t106 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 106 = 7762777065657174122294339663250022963822790749880973 := by
  rw [pow_two_pow_succ, t105]; decide
private theorem t107 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 107 = 6306215687365224286800077498519254367868688583932784 := by
  rw [pow_two_pow_succ, t106]; decide
private theorem t108 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 108 = 3833734437255722865473400921860824727778490949778348 := by
  rw [pow_two_pow_succ, t107]; decide
private theorem t109 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 109 = 7666814897648162181162996855746188323865912072987636 := by
  rw [pow_two_pow_succ, t108]; decide
private theorem t110 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 110 = 4374123092571622227999717052066672298935423014001605 := by
  rw [pow_two_pow_succ, t109]; decide
private theorem t111 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 111 = 9124416931583035776945152972616564722576915215096408 := by
  rw [pow_two_pow_succ, t110]; decide
private theorem t112 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 112 = 7124857711350881331999550530355277616519488124723543 := by
  rw [pow_two_pow_succ, t111]; decide
private theorem t113 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 113 = 1906819888844600210281446090892311991962052391769432 := by
  rw [pow_two_pow_succ, t112]; decide
private theorem t114 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 114 = 9453742807362610069426017047619829155398533973552251 := by
  rw [pow_two_pow_succ, t113]; decide
private theorem t115 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 115 = 5078584198297283775208448700358979820163249132975381 := by
  rw [pow_two_pow_succ, t114]; decide
private theorem t116 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 116 = 1749562155950906169018586743754529550356422606059416 := by
  rw [pow_two_pow_succ, t115]; decide
private theorem t117 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 117 = 6496184479868275620952915631319793804146372077667410 := by
  rw [pow_two_pow_succ, t116]; decide
private theorem t118 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 118 = 7751927469641759026716538392224618880760626215590965 := by
  rw [pow_two_pow_succ, t117]; decide
private theorem t119 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 119 = 4342868763375136846241847794558775106691132872097774 := by
  rw [pow_two_pow_succ, t118]; decide
private theorem t120 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 120 = 9009931584666991169303594103161702725064135205952554 := by
  rw [pow_two_pow_succ, t119]; decide
private theorem t121 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 121 = 1876330810624427729290434820364081208760240363902822 := by
  rw [pow_two_pow_succ, t120]; decide
private theorem t122 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 122 = 2907777683915163480805691083879267562353127177293944 := by
  rw [pow_two_pow_succ, t121]; decide
private theorem t123 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 123 = 8953790136491311425019308613644427539245160031729105 := by
  rw [pow_two_pow_succ, t122]; decide
private theorem t124 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 124 = 10249569469461811631426527163449211368052042122113276 := by
  rw [pow_two_pow_succ, t123]; decide
private theorem t125 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 125 = 2788788602361898046640822352181699315998834330952800 := by
  rw [pow_two_pow_succ, t124]; decide
private theorem t126 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 126 = 9024399888213393365851066370546737614897298724524786 := by
  rw [pow_two_pow_succ, t125]; decide
private theorem t127 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 127 = 7768445714457887875490275812312546131195886351534765 := by
  rw [pow_two_pow_succ, t126]; decide
private theorem t128 :
    (3 : ZMod Q) ^ (2:ℕ) ^ 128 = 2316527375723807742372773799812395978426193241580707 := by
  rw [pow_two_pow_succ, t127]; decide

/-! ## The Proth coefficient power `3 ^ K` -/

private theorem hx :
    (3 : ZMod Q) ^ (30532933579843:ℕ) =
      8867217711494650957288072693031600856125081676807220 := by
  rw [show (30532933579843:ℕ) = 2^44 + 2^43 + 2^41 + 2^40 + 2^39 + 2^38 + 2^34 + 2^32 + 2^23 +
    2^21 + 2^19 + 2^15 + 2^14 + 2^13 + 2^12 + 2^10 + 2^6 + 2^1 + 2^0 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
    t44, t43, t41, t40, t39, t38, t34, t32, t23, t21, t19, t15, t14, t13, t12, t10, t6, t1, t0]
  decide

/-! ## Repeated-squaring chain for `x = 3 ^ K` -/

private theorem u0 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 0 =
      8867217711494650957288072693031600856125081676807220 := by
  norm_num
private theorem u1 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 1 =
      5498647032610797440551921636356253187995807461949233 := by
  rw [pow_two_pow_succ, u0]; decide
private theorem u2 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 2 =
      5527711520975374237955151970065609078541284685725389 := by
  rw [pow_two_pow_succ, u1]; decide
private theorem u3 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 3 =
      7373172800898036042094375597615261205578573908438550 := by
  rw [pow_two_pow_succ, u2]; decide
private theorem u4 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 4 =
      6037348775667592214107003618220620567457878387757095 := by
  rw [pow_two_pow_succ, u3]; decide
private theorem u5 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 5 =
      5161853778174128535454651639797447830898479817892301 := by
  rw [pow_two_pow_succ, u4]; decide
private theorem u6 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 6 =
      3599606348675635650090649006617530299027414417783549 := by
  rw [pow_two_pow_succ, u5]; decide
private theorem u7 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 7 =
      7353972378655159765471191897249013117277328925037653 := by
  rw [pow_two_pow_succ, u6]; decide
private theorem u8 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 8 =
      5960824427390577716181335195396525403417583307298396 := by
  rw [pow_two_pow_succ, u7]; decide
private theorem u9 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 9 =
      8972856145593171981054651304218206705093865513856375 := by
  rw [pow_two_pow_succ, u8]; decide
private theorem u10 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 10 =
      1418461011623605028171562735547379979031908534872861 := by
  rw [pow_two_pow_succ, u9]; decide
private theorem u11 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 11 =
      10333673032613662871376959452785562409696863599566251 := by
  rw [pow_two_pow_succ, u10]; decide
private theorem u12 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 12 =
      2546415011420510312528987854922550405145586208482125 := by
  rw [pow_two_pow_succ, u11]; decide
private theorem u13 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 13 =
      6764193658994157332577481330880731951583819222532340 := by
  rw [pow_two_pow_succ, u12]; decide
private theorem u14 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 14 =
      275155163708232371372635398142750465290094914764592 := by
  rw [pow_two_pow_succ, u13]; decide
private theorem u15 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 15 =
      5337641309773078694780578790049657593966860866041154 := by
  rw [pow_two_pow_succ, u14]; decide
private theorem u16 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 16 =
      4637450037960181332681620070895583792123974956216347 := by
  rw [pow_two_pow_succ, u15]; decide
private theorem u17 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 17 =
      2337795266782682117125238229482436212752936914727718 := by
  rw [pow_two_pow_succ, u16]; decide
private theorem u18 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 18 =
      2926534283578550750069395447250755345612352674304632 := by
  rw [pow_two_pow_succ, u17]; decide
private theorem u19 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 19 =
      1674632705197671833025499614477087041572907386924461 := by
  rw [pow_two_pow_succ, u18]; decide
private theorem u20 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 20 =
      978104409918391902813182784548236741245781869461126 := by
  rw [pow_two_pow_succ, u19]; decide
private theorem u21 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 21 =
      9313881406875331897669666609316227706808077118933777 := by
  rw [pow_two_pow_succ, u20]; decide
private theorem u22 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 22 =
      616495931336508463472423891959970469173419657517213 := by
  rw [pow_two_pow_succ, u21]; decide
private theorem u23 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 23 =
      7569286065235454183524616675755747084749975285951897 := by
  rw [pow_two_pow_succ, u22]; decide
private theorem u24 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 24 =
      4007024699017374501213250829112176085756320227037234 := by
  rw [pow_two_pow_succ, u23]; decide
private theorem u25 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 25 =
      1480531184413687138527988200001489744015041703941588 := by
  rw [pow_two_pow_succ, u24]; decide
private theorem u26 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 26 =
      5444166289811904943701414919714057394090636001558269 := by
  rw [pow_two_pow_succ, u25]; decide
private theorem u27 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 27 =
      8007772875309733093315482797849379496271541209707315 := by
  rw [pow_two_pow_succ, u26]; decide
private theorem u28 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 28 =
      8831469683938935255738246012720455477001639199750624 := by
  rw [pow_two_pow_succ, u27]; decide
private theorem u29 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 29 =
      1251494618797828800800154719871156598851249416105597 := by
  rw [pow_two_pow_succ, u28]; decide
private theorem u30 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 30 =
      5279614351633619776116627222771207413807958735410897 := by
  rw [pow_two_pow_succ, u29]; decide
private theorem u31 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 31 =
      3006979714151795345095503467048517943179038526552464 := by
  rw [pow_two_pow_succ, u30]; decide
private theorem u32 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 32 =
      7365606227575110323378217355254835437315151200143635 := by
  rw [pow_two_pow_succ, u31]; decide
private theorem u33 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 33 =
      5747370655389854214416834743742914683264023372943663 := by
  rw [pow_two_pow_succ, u32]; decide
private theorem u34 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 34 =
      7297573659191523263515382519393395270683899186147185 := by
  rw [pow_two_pow_succ, u33]; decide
private theorem u35 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 35 =
      3820209135087971872465734918731706957667130064990436 := by
  rw [pow_two_pow_succ, u34]; decide
private theorem u36 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 36 =
      8390930369102252507540944568664143256280396913044774 := by
  rw [pow_two_pow_succ, u35]; decide
private theorem u37 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 37 =
      5129848308999741772733283521299552527027697796700365 := by
  rw [pow_two_pow_succ, u36]; decide
private theorem u38 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 38 =
      978792223909163244495852316955660103744264316016282 := by
  rw [pow_two_pow_succ, u37]; decide
private theorem u39 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 39 =
      7728326605909993736621800873964875531707771711269959 := by
  rw [pow_two_pow_succ, u38]; decide
private theorem u40 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 40 =
      4283668328405581222638358035422959895995992248874068 := by
  rw [pow_two_pow_succ, u39]; decide
private theorem u41 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 41 =
      2740305079358451974957635335711801598616282250567174 := by
  rw [pow_two_pow_succ, u40]; decide
private theorem u42 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 42 =
      7223813330881905079826246661693565276874020583117725 := by
  rw [pow_two_pow_succ, u41]; decide
private theorem u43 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 43 =
      6834964510141034541675659286264299482001269680374030 := by
  rw [pow_two_pow_succ, u42]; decide
private theorem u44 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 44 =
      4596038993181684689288772844923090827442984536938789 := by
  rw [pow_two_pow_succ, u43]; decide
private theorem u45 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 45 =
      781282775540255018188211930692328159728220208089461 := by
  rw [pow_two_pow_succ, u44]; decide
private theorem u46 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 46 =
      4141105578165326349124670149437599377488457992394003 := by
  rw [pow_two_pow_succ, u45]; decide
private theorem u47 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 47 =
      2807387292354361584550574631503458488385920053980310 := by
  rw [pow_two_pow_succ, u46]; decide
private theorem u48 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 48 =
      6784024883899749737100018725243000394596122156886845 := by
  rw [pow_two_pow_succ, u47]; decide
private theorem u49 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 49 =
      9095626602435879984971290895431449508822455661910130 := by
  rw [pow_two_pow_succ, u48]; decide
private theorem u50 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 50 =
      5313653031205315844614430734095637321883110748985347 := by
  rw [pow_two_pow_succ, u49]; decide
private theorem u51 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 51 =
      6692720398606938029651794486526160956657136302434379 := by
  rw [pow_two_pow_succ, u50]; decide
private theorem u52 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 52 =
      5262544112769781956133423850585274653791145382743468 := by
  rw [pow_two_pow_succ, u51]; decide
private theorem u53 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 53 =
      247710395615809539147101761355208875323619230795341 := by
  rw [pow_two_pow_succ, u52]; decide
private theorem u54 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 54 =
      8810303645380046924124296631520574561399817618463050 := by
  rw [pow_two_pow_succ, u53]; decide
private theorem u55 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 55 =
      3604614197408104795190577581832555021567220245480535 := by
  rw [pow_two_pow_succ, u54]; decide
private theorem u56 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 56 =
      3555513503107257784798813700007275585415652239996447 := by
  rw [pow_two_pow_succ, u55]; decide
private theorem u57 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 57 =
      6106362751292791973612306540799286262847808559992514 := by
  rw [pow_two_pow_succ, u56]; decide
private theorem u58 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 58 =
      1173720931252796675822330652291089769738946481353283 := by
  rw [pow_two_pow_succ, u57]; decide
private theorem u59 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 59 =
      3486954928981063328257471545330202967356418148084141 := by
  rw [pow_two_pow_succ, u58]; decide
private theorem u60 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 60 =
      7847235382869639079729282722233480398492540352357701 := by
  rw [pow_two_pow_succ, u59]; decide
private theorem u61 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 61 =
      5912551129371550184245064366585984091310692217211630 := by
  rw [pow_two_pow_succ, u60]; decide
private theorem u62 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 62 =
      1433979561950563353645366661162503419629740356288303 := by
  rw [pow_two_pow_succ, u61]; decide
private theorem u63 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 63 =
      2698274288689644527643194198828736714138833159546393 := by
  rw [pow_two_pow_succ, u62]; decide
private theorem u64 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 64 =
      8673379642739826811846513477844115642410287355404281 := by
  rw [pow_two_pow_succ, u63]; decide
private theorem u65 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 65 =
      4711912863890907936919827864217433042194821475934709 := by
  rw [pow_two_pow_succ, u64]; decide
private theorem u66 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 66 =
      10315008595574556877266661391219925101850446307480068 := by
  rw [pow_two_pow_succ, u65]; decide
private theorem u67 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 67 =
      9258556965053538913723990177132735941599059054782313 := by
  rw [pow_two_pow_succ, u66]; decide
private theorem u68 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 68 =
      8108988140237582418504853660037312669624080346629967 := by
  rw [pow_two_pow_succ, u67]; decide
private theorem u69 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 69 =
      9316548223627753239128695644149991736578335412196554 := by
  rw [pow_two_pow_succ, u68]; decide
private theorem u70 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 70 =
      3468254385107272399766244675109029352192532111951680 := by
  rw [pow_two_pow_succ, u69]; decide
private theorem u71 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 71 =
      163118874430696882067897519319985139576632716842189 := by
  rw [pow_two_pow_succ, u70]; decide
private theorem u72 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 72 =
      1429884414063047270956513846606174923207175028896725 := by
  rw [pow_two_pow_succ, u71]; decide
private theorem u73 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 73 =
      4148948287061603650365108395757591253791988386531540 := by
  rw [pow_two_pow_succ, u72]; decide
private theorem u74 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 74 =
      6471609239841022104195966129224025003828465611680587 := by
  rw [pow_two_pow_succ, u73]; decide
private theorem u75 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 75 =
      7406547981932158555514527834976027541682034909132614 := by
  rw [pow_two_pow_succ, u74]; decide
private theorem u76 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 76 =
      3355978029871679142983124364349467477557402497009483 := by
  rw [pow_two_pow_succ, u75]; decide
private theorem u77 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 77 =
      3094122429366323638494210452823548675571221454523015 := by
  rw [pow_two_pow_succ, u76]; decide
private theorem u78 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 78 =
      6809606818679267643578930972865938126589321881576300 := by
  rw [pow_two_pow_succ, u77]; decide
private theorem u79 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 79 =
      6971474645470680215525649370590255318844241036589444 := by
  rw [pow_two_pow_succ, u78]; decide
private theorem u80 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 80 =
      665530999853329800842063908661562581425249242639714 := by
  rw [pow_two_pow_succ, u79]; decide
private theorem u81 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 81 =
      1459233590337867633137148821201784019269547165363785 := by
  rw [pow_two_pow_succ, u80]; decide
private theorem u82 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 82 =
      7403231269740069694541360201962635570375275592305085 := by
  rw [pow_two_pow_succ, u81]; decide
private theorem u83 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 83 =
      3475032177642704749527852055106448456083154577582968 := by
  rw [pow_two_pow_succ, u82]; decide
private theorem u84 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 84 =
      495825317723505549641065113843108285772624707463311 := by
  rw [pow_two_pow_succ, u83]; decide
private theorem u85 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 85 =
      8095739197200813651749963313723832255080950096190103 := by
  rw [pow_two_pow_succ, u84]; decide
private theorem u86 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 86 =
      10313136321136598172670165768810026632836960070048171 := by
  rw [pow_two_pow_succ, u85]; decide
private theorem u87 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 87 =
      7772498169254211507875040831096946810794518893369157 := by
  rw [pow_two_pow_succ, u86]; decide
private theorem u88 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 88 =
      5970521287647749339831986851506083162819959240089427 := by
  rw [pow_two_pow_succ, u87]; decide
private theorem u89 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 89 =
      950986550492005245405700121571766617683035375536193 := by
  rw [pow_two_pow_succ, u88]; decide
private theorem u90 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 90 =
      9660193565596953313273113020620123235202338244242929 := by
  rw [pow_two_pow_succ, u89]; decide
private theorem u91 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 91 =
      10330110456755546887812905129198784071461343096149301 := by
  rw [pow_two_pow_succ, u90]; decide
private theorem u92 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 92 =
      8238255368997011340415744141743982592028802900347281 := by
  rw [pow_two_pow_succ, u91]; decide
private theorem u93 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 93 =
      5552747192099323852650731734504509834133220556927256 := by
  rw [pow_two_pow_succ, u92]; decide
private theorem u94 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 94 =
      4544260040681843442525768334217111780501743676412443 := by
  rw [pow_two_pow_succ, u93]; decide
private theorem u95 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 95 =
      3294678675724442209344591861603356775105868894708282 := by
  rw [pow_two_pow_succ, u94]; decide
private theorem u96 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 96 =
      3836100787875010566497249445808992732672294734397287 := by
  rw [pow_two_pow_succ, u95]; decide
private theorem u97 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 97 =
      1159897189367043602818722557706071139794640113646564 := by
  rw [pow_two_pow_succ, u96]; decide
private theorem u98 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 98 =
      1477087411064345891266568933251794414929172641700591 := by
  rw [pow_two_pow_succ, u97]; decide
private theorem u99 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 99 =
      8930145055258949444661236035925357331806235243763035 := by
  rw [pow_two_pow_succ, u98]; decide
private theorem u100 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 100 =
      9692325118921805735970419716048644492567275151043829 := by
  rw [pow_two_pow_succ, u99]; decide
private theorem u101 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 101 =
      841651266625864549856687257302270568014183106015022 := by
  rw [pow_two_pow_succ, u100]; decide
private theorem u102 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 102 =
      6075622972598204586891125247850440078653592277292697 := by
  rw [pow_two_pow_succ, u101]; decide
private theorem u103 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 103 =
      6308242180430551011181343423589872037447126932052647 := by
  rw [pow_two_pow_succ, u102]; decide
private theorem u104 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 104 =
      9094592019996464866679857138978318039216358761127849 := by
  rw [pow_two_pow_succ, u103]; decide
private theorem u105 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 105 =
      7660125473243899658003593530328639311421651800326683 := by
  rw [pow_two_pow_succ, u104]; decide
private theorem u106 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 106 =
      4208835754663513451651231760692851953874193953411969 := by
  rw [pow_two_pow_succ, u105]; decide
private theorem u107 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 107 =
      3132028892835326220940683394584764345168385125719815 := by
  rw [pow_two_pow_succ, u106]; decide
private theorem u108 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 108 =
      4839960421314553479730853313796873142457551478385981 := by
  rw [pow_two_pow_succ, u107]; decide
private theorem u109 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 109 =
      8258015311061404925392729640360280671947877556303856 := by
  rw [pow_two_pow_succ, u108]; decide
private theorem u110 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 110 =
      8252704184737820736950544521745454924677335197806075 := by
  rw [pow_two_pow_succ, u109]; decide
private theorem u111 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 111 =
      6686370793463276631445377895122916571412770828977190 := by
  rw [pow_two_pow_succ, u110]; decide
private theorem u112 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 112 =
      7638629961826811908498609599760042910646753504406915 := by
  rw [pow_two_pow_succ, u111]; decide
private theorem u113 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 113 =
      2429451331983605634368931798695962404081350686301345 := by
  rw [pow_two_pow_succ, u112]; decide
private theorem u114 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 114 =
      657595178499221433575836564125738427409768417847553 := by
  rw [pow_two_pow_succ, u113]; decide
private theorem u115 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 115 =
      5046666221866757637262617728759971093864070926949325 := by
  rw [pow_two_pow_succ, u114]; decide
private theorem u116 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 116 =
      3822069042135057854112894777381763444869694040554145 := by
  rw [pow_two_pow_succ, u115]; decide
private theorem u117 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 117 =
      4407645485744942413573496981325147783198774467577706 := by
  rw [pow_two_pow_succ, u116]; decide
private theorem u118 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 118 =
      9653864418839601364075697561740585439790713959020768 := by
  rw [pow_two_pow_succ, u117]; decide
private theorem u119 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 119 =
      8843435609607980586379159854828964156895379956416237 := by
  rw [pow_two_pow_succ, u118]; decide
private theorem u120 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 120 =
      4325889815761581160768520754851946005503687838588229 := by
  rw [pow_two_pow_succ, u119]; decide
private theorem u121 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 121 =
      8774821922046699490606063441158261652034632660638073 := by
  rw [pow_two_pow_succ, u120]; decide
private theorem u122 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 122 =
      2144731885717562071235095443947924792408978771067975 := by
  rw [pow_two_pow_succ, u121]; decide
private theorem u123 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 123 =
      1751681094365919588343378063512783177386569210739768 := by
  rw [pow_two_pow_succ, u122]; decide
private theorem u124 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 124 =
      175141427653077195324030639278654947511770000286019 := by
  rw [pow_two_pow_succ, u123]; decide
private theorem u125 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 125 =
      8077584576943474533263921731702049911630433274442391 := by
  rw [pow_two_pow_succ, u124]; decide
private theorem u126 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 126 =
      9122806315231936535995566548109023987907216919049517 := by
  rw [pow_two_pow_succ, u125]; decide
private theorem u127 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 127 =
      10389818907588778884587886312609003368974655483281408 := by
  rw [pow_two_pow_succ, u126]; decide
private theorem u128 :
    (8867217711494650957288072693031600856125081676807220 : ZMod Q) ^ (2:ℕ) ^ 128 =
      1 := by
  rw [pow_two_pow_succ, u127]; decide

/-! ## The outer Lucas primality certificate -/

private theorem cert_main : (3 : ZMod Q) ^ (Q - 1) = 1 := by
  rw [show Q - 1 = K * 2 ^ 128 from by norm_num, pow_mul, hx, u128]

private theorem cert_q2 : (3 : ZMod Q) ^ ((Q - 1) / 2) ≠ 1 := by
  rw [show (Q - 1) / 2 = K * 2 ^ 127 from by norm_num, pow_mul, hx, u127]
  decide

private theorem cert_qh : (3 : ZMod Q) ^ ((Q - 1) / K) ≠ 1 := by
  rw [show (Q - 1) / K = 2 ^ 128 from by norm_num, t128]
  decide

/-- **The 173-bit Proth prime certificate.**  Outer Lucas run at base 3, consuming the
inner certificate `prime_K` for the Proth coefficient. -/
theorem prime_Q : Nat.Prime Q := by
  refine lucas_primality Q 3 cert_main ?_
  intro q hq hdvd
  rw [show Q - 1 = K * 2 ^ 128 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · have hqh : q = K := (Nat.prime_dvd_prime_iff_eq hq prime_K).mp h
    subst hqh
    exact cert_qh
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst hq2
    exact cert_q2

local instance fact_prime_Q : Fact (Nat.Prime Q) := ⟨prime_Q⟩

private theorem g_def :
    (3 : ZMod Q) ^ ((Q - 1) / 64) =
      2144731885717562071235095443947924792408978771067975 := by
  rw [show (Q - 1) / 64 = K * 2 ^ 122 from by norm_num, pow_mul, hx, u122]

/-- The order-64 certificate for the dimension-15 rung. -/
theorem orderOf_gQ :
    orderOf (2144731885717562071235095443947924792408978771067975 : ZMod Q) = 64 := by
  have h5 : ¬ (2144731885717562071235095443947924792408978771067975 : ZMod Q) ^ (2:ℕ) ^ 5 = 1 := by
    decide
  have h6 : (2144731885717562071235095443947924792408978771067975 : ZMod Q) ^ (2:ℕ) ^ 6 = 1 := by
    decide
  have h := orderOf_eq_prime_pow
    (x := (2144731885717562071235095443947924792408978771067975 : ZMod Q)) h5 h6
  norm_num at h
  exact h

/-! ## The conditional pin -/

private theorem choose_64_16 : (64 : ℕ).choose 16 = 488526937079580 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide
private theorem choose_32_16 : (32 : ℕ).choose 16 = 601080390 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- The certified prime `Q` **inhabits** the `r = 16` literal-budget band.

`Mu6LiteralBands.mu6_band_open_r16` proves this band is nonempty; since the window is only
`≈ 0.368` bits wide, exhibiting an actual certified prime inside it is the substantive
step, and it is what the pin below consumes. -/
theorem Q_mem_band_r16 :
    (2 ^ 6).choose 16 / 16 * 2 ^ 128 ≤ Q ∧ Q < 2 ^ 16 * (2 ^ 5).choose 16 * 2 ^ 128 := by
  refine ⟨?_, ?_⟩
  · have h : (2 ^ 6 : ℕ).choose 16 / 16 = 30532933567473 := by
      rw [show (2 ^ 6 : ℕ) = 64 from by norm_num, choose_64_16]
    rw [h]; norm_num
  · have h : (2 ^ 16 : ℕ) * (2 ^ 5 : ℕ).choose 16 = 39392404439040 := by
      rw [show (2 ^ 5 : ℕ) = 32 from by norm_num, choose_32_16]
      norm_num
    rw [h]; norm_num

/-- **The μ = 6 conditional literal-budget pin at rate 15/64**: given only the in-tree
divisibility hypothesis, `δ* = 48/64 = 3/4` exactly at `ε* = 2⁻¹²⁸` for the dimension-15
code on the 64-point smooth domain — beyond Johnson (`1 - √(15/64) ≈ 0.516`), and exactly
`1/64` below capacity (`49/64`). -/
theorem deltaStar_pin_mu6_dim15_of_not_dvd
    (hndvd : ∀ d₁ ∈ sigData (2 ^ 5) 16, ∀ d₂ ∈ sigData (2 ^ 5) 16,
      d₁ ≠ d₂ → ¬ (Q : ℤ) ∣ collisionResultant 6 d₁ d₂) :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (2144731885717562071235095443947924792408978771067975 : ZMod Q) 64 14)
        (1 / 2 ^ 128)
      = 48 / 64 := by
  haveI : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have h := Mu6ConditionalPin.kkh26_march_deltaStar_pin_of_not_dvd (p := Q) (μ := 6) (r := 16)
    (g := (2144731885717562071235095443947924792408978771067975 : ZMod Q)) (n := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact orderOf_gQ) (by norm_num) hndvd
    (1 / 2 ^ 128) ?hlo ?hhi
  case hlo =>
    have hc : ((64 : ℕ).choose 16 / 16 : ℕ) = 30532933567473 := by rw [choose_64_16]
    rw [hc]
    exact band_lo_general (by norm_num) (by norm_num)
  case hhi =>
    have hc : (2 ^ 16 * (2 ^ (6 - 1)).choose 16 : ℕ) = 39392404439040 := by
      change (2 ^ 16 * (32 : ℕ).choose 16 : ℕ) = 39392404439040
      rw [choose_32_16]
      norm_num
    rw [hc]
    exact band_hi_general (e := 39392404439039) (q := Q) (by norm_num)
  rw [h]
  have e2 : (((16 : ℕ)) : ℝ≥0) = (16 : ℝ≥0) := by norm_num
  rw [e2]
  have hd : (16 : ℝ≥0) / ((2 : ℝ≥0) ^ 6) = 16 / 64 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- The certified prime `Q` clears the μ = 6 squared Landau envelope `2^255 < Q^2`.  The
envelope does not depend on `r`, which is why this rung reuses the `r = 5` analytic input
verbatim. -/
theorem landauSqEnvelope_mu6_lt_Q_sq : landauSqEnvelope (2 ^ 5) < Q ^ 2 := by
  have hstrict : landauSqEnvelope (2 ^ 5) < (2 ^ 128 : ℕ) ^ 2 := by
    rw [Mu6ConditionalPin.landauSqEnvelope_mu6_eq_two_pow_255]
    norm_num
  have hq : 2 ^ 128 ≤ Q := by norm_num [Q]
  exact lt_of_lt_of_le hstrict (Nat.pow_le_pow_left hq 2)

/-- **Cyclotomic Landau handoff for the rate-15/64 rung.** -/
theorem deltaStar_pin_mu6_dim15_of_cyclotomicLandauSqBound
    (hL : cyclotomicLandauSqBound 6) :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (2144731885717562071235095443947924792408978771067975 : ZMod Q) 64 14)
        (1 / 2 ^ 128)
      = 48 / 64 := by
  exact deltaStar_pin_mu6_dim15_of_not_dvd
    (collisionResultant_not_dvd_of_cyclotomicLandauSqBound (p := Q)
      (m := 6) (r := 16) hL (by norm_num) (by norm_num)
      landauSqEnvelope_mu6_lt_Q_sq)

/-- **Promoted μ = 6 dimension-15 literal pin.**  `δ* = 3/4` at `ε* = 2^-128` for the
rate-`15/64` code on the 64-point smooth domain, with no remaining named hypothesis.
This is the top rung of the μ = 6 ladder: `Mu6LiteralBands.mu6_band_closed_r17` shows no
`r ≥ 17` rung exists. -/
theorem deltaStar_pin_mu6_dim15 :
    mcaDeltaStar (F := ZMod Q) (A := ZMod Q)
        (evalCode
          (2144731885717562071235095443947924792408978771067975 : ZMod Q) 64 14)
        (1 / 2 ^ 128)
      = 48 / 64 := by
  exact deltaStar_pin_mu6_dim15_of_cyclotomicLandauSqBound
    (cyclotomicLandauSqBound_proved (m := 6) (by norm_num))

#print axioms ArkLib.ProximityGap.Mu6Dim15Pin.prime_K
#print axioms ArkLib.ProximityGap.Mu6Dim15Pin.prime_Q
#print axioms ArkLib.ProximityGap.Mu6Dim15Pin.orderOf_gQ
#print axioms ArkLib.ProximityGap.Mu6Dim15Pin.Q_mem_band_r16
#print axioms ArkLib.ProximityGap.Mu6Dim15Pin.landauSqEnvelope_mu6_lt_Q_sq
#print axioms ArkLib.ProximityGap.Mu6Dim15Pin.deltaStar_pin_mu6_dim15

end ArkLib.ProximityGap.Mu6Dim15Pin
