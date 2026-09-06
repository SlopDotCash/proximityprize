/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.KKH26StratifiedSpread
import ArkLib.Data.CodingTheory.ProximityGap.SubCeilingLadder
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# The stratified KKH26 ceiling at exact rate one half

`KKH26StratifiedSpread.kkh26_stratified_epsMCA_lower_bound` reaches radii with
`r > 2^(mu-1)`, but is stated only for degree `(r - 2) * m`.
`SubCeilingLadder.subceiling_epsMCA_lower_bound` permits every degree in the window

`(r - 2) * m <= D < (r - 1) * m`,

but uses only the unstratified `j = 0` count and therefore assumes `r <= 2^(mu-1)`.
This file combines the two independent upgrades.  At

`r = 2^(mu-1) + 1`, `D = 2^(mu-1) * m - 1`,

the code dimension is exactly `2^(mu-1) * m = n / 2`; the feasible `j = 1` stratum
is nonempty and gives the first KKH26 bad-line ceiling for the exact rate-`1/2` code.

The result still assumes the large-prime resultant-separation hypothesis
`p > (2^mu)^(2^(mu-1))`.  It does not provide the good side of the MCA threshold and
does not discharge the polynomial-field `InteriorCeiling` input.
-/

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.KKH26

/-- Injectivity of `i |-> g^i` below the order of `g`. -/
private lemma pow_inj_below_order_stratified
    {F : Type*} [Field F] {g : F} (hg0 : g ≠ 0) {N : ℕ} (hg : orderOf g = N) :
    ∀ i, i < N → ∀ j, j < N → g ^ i = g ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → g ^ i = g ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have hmul : g ^ i * g ^ (j - i) = g ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have hone : g ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i hg0) hmul
    have hdvd : N ∣ j - i := hg ▸ orderOf_dvd_of_pow_eq_one hone
    have hzero : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

open Classical in
/-- **Degree-decoupled stratified KKH26 spread.**  The full antipodal-stratified
subset-sum numerator remains valid for every degree in the KKH26 compatibility window.
In particular, unlike the unstratified degree-decoupled theorem, this applies throughout
the full range `2 <= r <= 2^mu`. -/
theorem kkh26_stratified_subceiling_epsMCA_lower_bound
    {p n : ℕ} [Fact p.Prime] [NeZero n] {mu m r D : ℕ}
    (hmu : 1 ≤ mu) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ mu * m)
    (hg : orderOf g = 2 ^ mu * m)
    (hp : ((2 : ℕ) ^ mu) ^ 2 ^ (mu - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ mu)
    (hDlow : (r - 2) * m ≤ D) (hDhigh : D < (r - 1) * m) :
    ((∑ j ∈ feasSet (2 ^ (mu - 1)) r,
        2 ^ (r - 2 * j) * (2 ^ (mu - 1)).choose (r - 2 * j) : ℕ) : ENNReal) /
        (p : ENNReal)
      ≤ epsMCA (F := ZMod p) (evalCode g n D)
          (1 - (r : NNReal) / ((2 : NNReal) ^ mu)) := by
  classical
  subst hn
  have hm0 : m ≠ 0 := by omega
  have hs1 : (1 : ℕ) ≤ 2 ^ mu := Nat.one_le_two_pow
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hzero : (0 : ZMod p) ^ (2 ^ mu * m) = 1 := by
      rw [← hg]
      exact pow_orderOf_eq_one 0
    rw [zero_pow (Nat.mul_ne_zero (by positivity) hm0)] at hzero
    exact zero_ne_one hzero
  have hgmord : orderOf (g ^ m) = 2 ^ mu := by
    have hone : (g ^ m) ^ (2 ^ mu) = 1 := by
      rw [← pow_mul, mul_comm m (2 ^ mu), ← hg]
      exact pow_orderOf_eq_one g
    have hupper : orderOf (g ^ m) ∣ 2 ^ mu := orderOf_dvd_of_pow_eq_one hone
    have hone' : g ^ (m * orderOf (g ^ m)) = 1 := by
      rw [pow_mul]
      exact pow_orderOf_eq_one (g ^ m)
    have hdvd : 2 ^ mu * m ∣ m * orderOf (g ^ m) :=
      hg ▸ orderOf_dvd_of_pow_eq_one hone'
    rw [mul_comm (2 ^ mu) m] at hdvd
    have hlower : 2 ^ mu ∣ orderOf (g ^ m) :=
      (Nat.mul_dvd_mul_iff_left (by omega : 0 < m)).mp hdvd
    exact Nat.dvd_antisymm hupper hlower
  have hprim : IsPrimitiveRoot (g ^ m) (2 ^ mu) := by
    have h := IsPrimitiveRoot.orderOf (g ^ m)
    rwa [hgmord] at h
  have hcount := kkh26_stratified_count hmu hprim hp r
  set Gsub : Finset (ZMod p) :=
    (range (2 ^ mu)).image (fun i => (g ^ m) ^ i) with hGsub
  set sums : Finset (ZMod p) :=
    (Gsub.powersetCard r).image (fun T => ∑ x ∈ T, x) with hsums
  set u : WordStack (ZMod p) (Fin 2) (Fin (2 ^ mu * m)) :=
    ![fun i => (g ^ (i : ℕ)) ^ (r * m),
      fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m)] with hu
  set Lambda : Finset (ZMod p) := sums.image (fun w => -w) with hLambda
  have hLambdaCard :
      (∑ j ∈ feasSet (2 ^ (mu - 1)) r,
        2 ^ (r - 2 * j) * (2 ^ (mu - 1)).choose (r - 2 * j)) ≤ Lambda.card := by
    rw [hLambda, card_image_of_injective _ neg_injective]
    exact hcount
  have hbad : ∀ gamma ∈ Lambda,
      mcaEvent (evalCode g (2 ^ mu * m) D)
        (1 - (r : NNReal) / ((2 : NNReal) ^ mu)) (u 0) (u 1) gamma := by
    intro gamma hgamma
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hgamma
    obtain ⟨T, hT, hTsum⟩ := mem_image.mp hw
    obtain ⟨hTG, hTcard⟩ := mem_powersetCard.mp hT
    obtain ⟨q, hqdeg, hqagree⟩ :=
      badline_pointwise_agreement hm T (by omega : 2 ≤ T.card)
    rw [hTcard] at hqdeg hqagree
    set S : Finset (Fin (2 ^ mu * m)) :=
      univ.filter (fun i => (g ^ (i : ℕ)) ^ m ∈ T) with hSdef
    have himg : (univ : Finset (Fin (2 ^ mu * m))).image
          (fun i : Fin (2 ^ mu * m) => g ^ (i : ℕ))
        = (range (2 ^ mu * m)).image (fun i => g ^ i) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, _, rfl⟩ := mem_image.mp hx
        exact mem_image.mpr ⟨(i : ℕ), mem_range.mpr i.isLt, rfl⟩
      · intro hx
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
        exact mem_image.mpr ⟨⟨i, mem_range.mp hi⟩, mem_univ _, rfl⟩
    have hSimg : S.image (fun i : Fin (2 ^ mu * m) => g ^ (i : ℕ))
        = ((range (2 ^ mu * m)).image (fun i => g ^ i)).filter
            (fun x => x ^ m ∈ T) := by
      rw [← himg, filter_image]
    have hScard : S.card = m * r := by
      have hcardImage :
          (S.image (fun i : Fin (2 ^ mu * m) => g ^ (i : ℕ))).card = S.card :=
        card_image_of_injOn (fun i _ j _ hij =>
          Fin.ext (pow_inj_below_order_stratified hg0 hg _ i.isLt _ j.isLt hij))
      rw [← hcardImage, hSimg, fiber_count hm hs1 hg T hTG, hTcard]
    refine ⟨S, ?_,
      ⟨fun i => q.eval (g ^ (i : ℕ)),
        ⟨q, le_trans hqdeg hDlow, fun _ => rfl⟩, ?_⟩, ?_⟩
    · have hcardFin : (Fintype.card (Fin (2 ^ mu * m)) : NNReal)
          = ((2 ^ mu * m : ℕ) : NNReal) := by
        rw [Fintype.card_fin]
      have hratio : (r : NNReal) / ((2 : NNReal) ^ mu) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hcast : (r : NNReal) ≤ ((2 ^ mu : ℕ) : NNReal) := by
          exact_mod_cast hr
        simpa [Nat.cast_pow] using hcast
      have hcomplement : (1 : NNReal) - (1 - (r : NNReal) / ((2 : NNReal) ^ mu))
          = (r : NNReal) / ((2 : NNReal) ^ mu) :=
        tsub_tsub_cancel_of_le hratio
      rw [hScard, hcardFin, hcomplement]
      have harith : ((r : NNReal) / ((2 : NNReal) ^ mu)) *
            ((2 ^ mu * m : ℕ) : NNReal) = ((m * r : ℕ) : NNReal) := by
        push_cast
        rw [div_mul_eq_mul_div, mul_comm (r : NNReal) _, mul_comm ((2 : NNReal) ^ mu) _,
          mul_assoc, mul_div_assoc,
          mul_div_cancel_left₀ _ (by positivity : ((2 : NNReal) ^ mu) ≠ 0)]
      rw [harith]
    · intro i hi
      have hxm : (g ^ (i : ℕ)) ^ m ∈ T := (mem_filter.mp hi).2
      have hpoint := hqagree (g ^ (i : ℕ)) hxm
      rw [hTsum] at hpoint
      rw [hu]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
      linear_combination -hpoint
    · rintro ⟨v0, _, v1, hv1, hpair⟩
      obtain ⟨q1, hq1deg, hq1⟩ := hv1
      have hSH : S.image (fun i : Fin (2 ^ mu * m) => g ^ (i : ℕ))
          ⊆ (range (2 ^ mu * m)).image (fun i => g ^ i) := by
        rw [hSimg]
        exact filter_subset _ _
      have hScard' : r * m ≤
          (S.image (fun i : Fin (2 ^ mu * m) => g ^ (i : ℕ))).card := by
        rw [hSimg, fiber_count hm hs1 hg T hTG, hTcard, mul_comm]
      refine subceiling_ca_failure (g := g) (n := 2 ^ mu * m) hm hDhigh _ hSH hScard'
        q1 hq1deg ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      have h1 : v1 i = u 1 i := (hpair i hi).2
      have h2 : v1 i = q1.eval (g ^ (i : ℕ)) := hq1 i
      rw [hu] at h1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [← h2, h1]
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g (2 ^ mu * m) D)
    (1 - (r : NNReal) / ((2 : NNReal) ^ mu)) u Lambda hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  exact ENNReal.div_le_div_right (by exact_mod_cast hLambdaCard) _

/-- The endpoint degree has the KKH26 compatibility window required by the combined
stratified theorem. -/
theorem stratified_exactRate_degree_window {m r : ℕ} (hm : 1 ≤ m) (hr2 : 2 ≤ r) :
    (r - 2) * m ≤ (r - 1) * m - 1 ∧
      (r - 1) * m - 1 < (r - 1) * m := by
  have hstep : (r - 2) * m < (r - 1) * m :=
    (Nat.mul_lt_mul_right hm).2 (by omega)
  have hpos : 0 < (r - 1) * m := Nat.mul_pos (by omega) hm
  omega

open Classical in
/-- **Exact rate-`1/2` KKH26 spread.**  Put `r = 2^(mu-1)+1` and use the endpoint
degree `D = 2^(mu-1)*m-1`.  The corresponding evaluation code has dimension
`2^(mu-1)*m`, exactly one half of `n = 2^mu*m`. -/
theorem kkh26_stratified_exactRateHalf_epsMCA_lower_bound
    {p n : ℕ} [Fact p.Prime] [NeZero n] {mu m : ℕ}
    (hmu : 1 ≤ mu) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ mu * m)
    (hg : orderOf g = 2 ^ mu * m)
    (hp : ((2 : ℕ) ^ mu) ^ 2 ^ (mu - 1) < p) :
    ((∑ j ∈ feasSet (2 ^ (mu - 1)) (2 ^ (mu - 1) + 1),
        2 ^ (2 ^ (mu - 1) + 1 - 2 * j) *
          (2 ^ (mu - 1)).choose (2 ^ (mu - 1) + 1 - 2 * j) : ℕ) : ENNReal) /
        (p : ENNReal)
      ≤ epsMCA (F := ZMod p) (evalCode g n (2 ^ (mu - 1) * m - 1))
          (1 - ((2 ^ (mu - 1) + 1 : ℕ) : NNReal) / ((2 : NNReal) ^ mu)) := by
  let r : ℕ := 2 ^ (mu - 1) + 1
  have hr2 : 2 ≤ r := by
    dsimp [r]
    have hpowpos : 0 < 2 ^ (mu - 1) := by positivity
    omega
  have hhalf : 2 ^ (mu - 1) * 2 = 2 ^ mu := by
    rw [← pow_succ, Nat.sub_add_cancel hmu]
  have hr : r ≤ 2 ^ mu := by
    dsimp [r]
    omega
  have hwindow := stratified_exactRate_degree_window hm hr2
  have hrm1 : (r - 1) * m - 1 = 2 ^ (mu - 1) * m - 1 := by
    dsimp [r]
  simpa only [r, hrm1] using
    kkh26_stratified_subceiling_epsMCA_lower_bound hmu hm hn hg hp hr2 hr
      hwindow.1 hwindow.2

/-- The new exact-rate-half numerator is genuinely nonempty: `j = 1` is a feasible
antipodal stratum at `r = 2^(mu-1)+1`. -/
theorem one_mem_exactRateHalf_feasSet {mu : ℕ} (hmu : 1 ≤ mu) :
    1 ∈ feasSet (2 ^ (mu - 1)) (2 ^ (mu - 1) + 1) := by
  rw [mem_feasSet]
  have hpos : 1 ≤ 2 ^ (mu - 1) := Nat.one_le_two_pow
  omega

open Classical in
/-- **Exact rate-`1/2` operational ceiling.**  Any target below the stratified
bad-scalar mass forces the operational MCA threshold to the radius
`1 - 1/2 - 1/2^mu`. -/
theorem kkh26_stratified_exactRateHalf_mcaDeltaStar_le
    {p n : ℕ} [Fact p.Prime] [NeZero n] {mu m : ℕ}
    (hmu : 1 ≤ mu) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ mu * m)
    (hg : orderOf g = 2 ^ mu * m)
    (hp : ((2 : ℕ) ^ mu) ^ 2 ^ (mu - 1) < p) (epsilonStar : ENNReal)
    (hepsilon : epsilonStar <
      ((∑ j ∈ feasSet (2 ^ (mu - 1)) (2 ^ (mu - 1) + 1),
          2 ^ (2 ^ (mu - 1) + 1 - 2 * j) *
            (2 ^ (mu - 1)).choose (2 ^ (mu - 1) + 1 - 2 * j) : ℕ) : ENNReal) /
          (p : ENNReal)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n (2 ^ (mu - 1) * m - 1)) epsilonStar
      ≤ 1 - ((2 ^ (mu - 1) + 1 : ℕ) : NNReal) / ((2 : NNReal) ^ mu) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hepsilon
      (kkh26_stratified_exactRateHalf_epsMCA_lower_bound hmu hm hn hg hp))

/-- The exact-rate endpoint dimension is exactly half the smooth-domain block length. -/
theorem exactRateHalf_dimension_twice {n mu m : ℕ} (hmu : 1 ≤ mu)
    (hn : n = 2 ^ mu * m) :
    2 * (2 ^ (mu - 1) * m) = n := by
  have hhalf : 2 ^ (mu - 1) * 2 = 2 ^ mu := by
    rw [← pow_succ, Nat.sub_add_cancel hmu]
  calc
    2 * (2 ^ (mu - 1) * m) = (2 ^ (mu - 1) * 2) * m := by ring
    _ = 2 ^ mu * m := by rw [hhalf]
    _ = n := hn.symm

/-- The endpoint evaluation code is the Reed--Solomon code of exact dimension `n/2`. -/
theorem exactRateHalf_evalCode_eq_rsCode
    {p n : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p} {mu m : ℕ}
    (hm : 1 ≤ m) (hg : orderOf g = n) :
    evalCode g n (2 ^ (mu - 1) * m - 1) =
      ((ProximityGap.SpikeFloor.rsCode
          (ProximityGap.Ownership.smoothDom g n hg) (2 ^ (mu - 1) * m) :
          Submodule (ZMod p) (Fin n → ZMod p)) : Set (Fin n → ZMod p)) := by
  have hpos : 0 < 2 ^ (mu - 1) * m := Nat.mul_pos (by positivity) hm
  have hdim : 2 ^ (mu - 1) * m - 1 + 1 = 2 ^ (mu - 1) * m := by omega
  simpa only [hdim] using
    ProximityGap.Ownership.evalCode_eq_rsCode hg (2 ^ (mu - 1) * m - 1)

end ArkLib.ProximityGap.KKH26

#print axioms ArkLib.ProximityGap.KKH26.kkh26_stratified_subceiling_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.KKH26.kkh26_stratified_exactRateHalf_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.KKH26.one_mem_exactRateHalf_feasSet
#print axioms ArkLib.ProximityGap.KKH26.kkh26_stratified_exactRateHalf_mcaDeltaStar_le
#print axioms ArkLib.ProximityGap.KKH26.exactRateHalf_dimension_twice
#print axioms ArkLib.ProximityGap.KKH26.exactRateHalf_evalCode_eq_rsCode
