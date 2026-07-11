/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKSevenSubsetOverlapDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS11GenericDepthDecomposition

/-!
# Correlated marked-sunflower constraints and the pure primitive obstruction

For nonnegative disjoint-petal masses `D_r`, the common-core transform

`W_k = sum_{r <= k} D_r * choose (n - 2*r) (k-r)`

does have genuine cross-row structure.  After `D_0=D_1=D_2=0`, its first four adjacent ratio
slacks are positive combinations of `D_4,...,D_7`; in particular

`(k-2) W_(k+1) >= (n-k-3) W_k`, for `3 <= k <= 6` and `n >= 14`.

This is the total-positivity/covariance information supplied by a nonnegative mixture of the
binomial completion laws.  Unfortunately its direction is a *lower* bound on the next row.  The
extreme ray `D_7=T`, all other `D_r=0`, has `W_2=...=W_6=0` and `W_7=T`.  Its generating
polynomial is

`T * z^7 * (1+z)^(n-14)`,

so it is itself a single real-rooted binomial law (the classical PF-infinity certificate), not a
pathological mixture.  Thus real-rootedness, ultra-log-concavity, total positivity, shadows, or
finite-difference inequalities valid for every such mixture cannot bound `W_7` from the lower
rows.  Quantitatively, the pure primitive Wick coefficient is `13!!=135135`, which exceeds the
production allowance `126871` by exactly `8264`: even hypothetical vanishing of every proper
depth leaves a `6.115...%` primitive improvement to prove arithmetically.

The file also records the stronger coordinate that remains viable.  The sunflower transform
holds **coefficientwise in the full signed-label histogram**, hence after every additive
character.  For FS11 depth seven, the characteristic-zero label can be placed in the finite
group `(Fin m -> ZMod 29)`: degree is below `m`, coefficients have absolute value at most `14`,
and reduction modulo `29` therefore reflects zero exactly.  This retains cancellation discarded
by the predicate `label != 0`; it still does not remove the pure `D_7` ray without new arithmetic
control of the primitive label distribution.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators Polynomial

namespace ArkLib.ProximityGap.Frontier.BGKSunflowerCorrelationNoGo

open BGKSevenSubsetOverlapDecomposition
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition

/-! ## Exact adjacent-row correlation slacks -/

def forwardThree (n d₃ _d₄ _d₅ _d₆ _d₇ : Rat) : Rat := d₃

def forwardFour (n d₃ d₄ _d₅ _d₆ _d₇ : Rat) : Rat :=
  (n - 6) * d₃ + d₄

def forwardFive (n d₃ d₄ d₅ _d₆ _d₇ : Rat) : Rat :=
  (n - 6) * (n - 7) / 2 * d₃ + (n - 8) * d₄ + d₅

def forwardSix (n d₃ d₄ d₅ d₆ _d₇ : Rat) : Rat :=
  (n - 6) * (n - 7) * (n - 8) / 6 * d₃ +
    (n - 8) * (n - 9) / 2 * d₄ + (n - 10) * d₅ + d₆

def forwardSeven (n d₃ d₄ d₅ d₆ d₇ : Rat) : Rat :=
  (n - 6) * (n - 7) * (n - 8) * (n - 9) / 24 * d₃ +
    (n - 8) * (n - 9) * (n - 10) / 6 * d₄ +
      (n - 10) * (n - 11) / 2 * d₅ + (n - 12) * d₆ + d₇

theorem ratioSlack_three_four (n d₃ d₄ d₅ d₆ d₇ : Rat) :
    forwardFour n d₃ d₄ d₅ d₆ d₇ -
      (n - 6) * forwardThree n d₃ d₄ d₅ d₆ d₇ = d₄ := by
  norm_num [forwardFour, forwardThree]

theorem ratioSlack_four_five (n d₃ d₄ d₅ d₆ d₇ : Rat) :
    2 * forwardFive n d₃ d₄ d₅ d₆ d₇ -
        (n - 7) * forwardFour n d₃ d₄ d₅ d₆ d₇ =
      (n - 9) * d₄ + 2 * d₅ := by
  norm_num [forwardFive, forwardFour]
  ring

theorem ratioSlack_five_six (n d₃ d₄ d₅ d₆ d₇ : Rat) :
    3 * forwardSix n d₃ d₄ d₅ d₆ d₇ -
        (n - 8) * forwardFive n d₃ d₄ d₅ d₆ d₇ =
      ((n - 8) * (n - 11) / 2) * d₄ +
        2 * (n - 11) * d₅ + 3 * d₆ := by
  norm_num [forwardSix, forwardFive]
  ring

theorem ratioSlack_six_seven (n d₃ d₄ d₅ d₆ d₇ : Rat) :
    4 * forwardSeven n d₃ d₄ d₅ d₆ d₇ -
        (n - 9) * forwardSix n d₃ d₄ d₅ d₆ d₇ =
      ((n - 8) * (n - 9) * (n - 13) / 6) * d₄ +
        (n - 10) * (n - 13) * d₅ +
          3 * (n - 13) * d₆ + 4 * d₇ := by
  norm_num [forwardSeven, forwardSix]
  ring

/-- The complete adjacent-row correlation furnished by nonnegative binomial completion masses.
Every inequality is a lower bound on the next row, so none supplies the required upper bound. -/
theorem nonnegative_onsetThree_correlated_growth
    (n d₃ d₄ d₅ d₆ d₇ : Rat) (hn : 14 ≤ n)
    (hd₄ : 0 ≤ d₄) (hd₅ : 0 ≤ d₅) (hd₆ : 0 ≤ d₆) (hd₇ : 0 ≤ d₇) :
    (n - 6) * forwardThree n d₃ d₄ d₅ d₆ d₇ ≤
        forwardFour n d₃ d₄ d₅ d₆ d₇ ∧
    (n - 7) * forwardFour n d₃ d₄ d₅ d₆ d₇ ≤
        2 * forwardFive n d₃ d₄ d₅ d₆ d₇ ∧
    (n - 8) * forwardFive n d₃ d₄ d₅ d₆ d₇ ≤
        3 * forwardSix n d₃ d₄ d₅ d₆ d₇ ∧
    (n - 9) * forwardSix n d₃ d₄ d₅ d₆ d₇ ≤
        4 * forwardSeven n d₃ d₄ d₅ d₆ d₇ := by
  constructor
  · have h := ratioSlack_three_four n d₃ d₄ d₅ d₆ d₇
    linarith
  constructor
  · have h := ratioSlack_four_five n d₃ d₄ d₅ d₆ d₇
    have hn9 : 0 ≤ n - 9 := by linarith
    nlinarith [mul_nonneg hn9 hd₄]
  constructor
  · have h := ratioSlack_five_six n d₃ d₄ d₅ d₆ d₇
    have hn8 : 0 ≤ n - 8 := by linarith
    have hn11 : 0 ≤ n - 11 := by linarith
    nlinarith [mul_nonneg hn8 hn11, mul_nonneg hn11 hd₅,
      mul_nonneg (mul_nonneg hn8 hn11) hd₄]
  · have h := ratioSlack_six_seven n d₃ d₄ d₅ d₆ d₇
    have hn8 : 0 ≤ n - 8 := by linarith
    have hn9 : 0 ≤ n - 9 := by linarith
    have hn10 : 0 ≤ n - 10 := by linarith
    have hn13 : 0 ≤ n - 13 := by linarith
    nlinarith [mul_nonneg hn8 hn9,
      mul_nonneg (mul_nonneg hn8 hn9) hn13,
      mul_nonneg hn10 hn13,
      mul_nonneg (mul_nonneg (mul_nonneg hn8 hn9) hn13) hd₄,
      mul_nonneg (mul_nonneg hn10 hn13) hd₅,
      mul_nonneg hn13 hd₆]

/-! ## The pure depth-seven extreme ray -/

/-- The truncated common-core transform on abstract nonnegative petal masses. -/
def sunflowerTransform (n k : Nat) (D : Nat → Nat) : Nat :=
  ∑ r ∈ Finset.range (k + 1), D r * (n - 2 * r).choose (k - r)

/-- The extreme ray supported only on the globally-disjoint depth-seven coordinate. -/
def pureDepthSevenMass (T : Nat) (r : Nat) : Nat := if r = 7 then T else 0

theorem pureDepthSevenMass_zero {T r : Nat} (hr : r ≠ 7) :
    pureDepthSevenMass T r = 0 := by
  simp [pureDepthSevenMass, hr]

theorem pureDepthSeven_transform_eq_zero {n T k : Nat} (hk : k < 7) :
    sunflowerTransform n k (pureDepthSevenMass T) = 0 := by
  unfold sunflowerTransform
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_range] at hr
  simp [pureDepthSevenMass, show r ≠ 7 by omega]

theorem pureDepthSeven_transform_seven (n T : Nat) :
    sunflowerTransform n 7 (pureDepthSevenMass T) = T := by
  norm_num [sunflowerTransform, pureDepthSevenMass, Finset.sum_range_succ]

/-- No collection of constraints on rows two through six can bound row seven on the positive
sunflower cone: all five lower rows can vanish while the seventh exceeds an arbitrary bound. -/
theorem lower_rows_do_not_bound_seven (n B : Nat) :
    ∃ D : Nat → Nat,
      D 0 = 0 ∧ D 1 = 0 ∧ D 2 = 0 ∧
      (∀ k, 2 ≤ k → k ≤ 6 → sunflowerTransform n k D = 0) ∧
      B < sunflowerTransform n 7 D := by
  refine ⟨pureDepthSevenMass (B + 1), ?_, ?_, ?_, ?_, ?_⟩
  · simp [pureDepthSevenMass]
  · simp [pureDepthSevenMass]
  · simp [pureDepthSevenMass]
  · intro k _hk2 hk6
    exact pureDepthSeven_transform_eq_zero (by omega)
  · rw [pureDepthSeven_transform_seven]
    omega

/-- Polynomial certificate for the pure ray.  Its only roots are `0` and `-1`; this is the
standard real-rooted/PF-infinity binomial law rather than an irregular cone element. -/
noncomputable def pureDepthSevenPolynomial (n T : Nat) : Rat[X] :=
  C (T : Rat) * (X ^ 7 * (1 + X) ^ (n - 14))

theorem pureDepthSevenPolynomial_coeff_of_seven_le
    (n T k : Nat) (hk : 7 ≤ k) :
    (pureDepthSevenPolynomial n T).coeff k =
      (T : Rat) * ((n - 14).choose (k - 7) : Nat) := by
  rw [pureDepthSevenPolynomial, coeff_C_mul, coeff_X_pow_mul', if_pos hk,
    coeff_one_add_X_pow]

theorem pureDepthSevenPolynomial_coeff_of_lt_seven
    (n T k : Nat) (hk : k < 7) :
    (pureDepthSevenPolynomial n T).coeff k = 0 := by
  rw [pureDepthSevenPolynomial, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega)]
  simp

theorem pureDepthSevenPolynomial_eval (n T : Nat) (x : Rat) :
    (pureDepthSevenPolynomial n T).eval x =
      (T : Rat) * x ^ 7 * (1 + x) ^ (n - 14) := by
  simp [pureDepthSevenPolynomial]
  ring

/-- Formal root localization: every root of the pure-ray polynomial is real and belongs to
`{0,-1}`. -/
theorem pureDepthSevenPolynomial_root_localization
    (n T : Nat) (hT : 0 < T) (x : Rat)
    (hx : (pureDepthSevenPolynomial n T).eval x = 0) :
    x = 0 ∨ x = -1 := by
  rw [pureDepthSevenPolynomial_eval] at hx
  have hT0 : (T : Rat) ≠ 0 := by exact_mod_cast hT.ne'
  rcases mul_eq_zero.mp hx with hprefix | hxrest
  · rcases mul_eq_zero.mp hprefix with hTzero | hx7
    · exact (hT0 hTzero).elim
    · exact Or.inl (eq_zero_of_pow_eq_zero hx7)
  · right
    have hone : 1 + x = 0 := eq_zero_of_pow_eq_zero hxrest
    linarith

def primitiveWickCoefficient : Nat := Nat.doubleFactorial 13
def productionInjectiveAllowance : Nat := 126871

theorem primitiveWickCoefficient_exact : primitiveWickCoefficient = 135135 := by
  norm_num [primitiveWickCoefficient, Nat.doubleFactorial]

/-- The pure primitive Wick ray alone exceeds the complete production allowance by `8264`. -/
theorem primitiveWick_exceeds_allowance_by_exactly_8264 :
    primitiveWickCoefficient = productionInjectiveAllowance + 8264 := by
  norm_num [primitiveWickCoefficient, productionInjectiveAllowance, Nat.doubleFactorial]

theorem production_allowance_strictly_below_primitiveWick :
    productionInjectiveAllowance < primitiveWickCoefficient := by
  norm_num [primitiveWickCoefficient, productionInjectiveAllowance, Nat.doubleFactorial]

/-- The allowed fraction is strictly between `93.8%` and `93.9%` of the primitive Wick ray. -/
theorem production_allowance_ratio_between_938_and_939_per_mille :
    938 * primitiveWickCoefficient < 1000 * productionInjectiveAllowance ∧
      1000 * productionInjectiveAllowance < 939 * primitiveWickCoefficient := by
  norm_num [primitiveWickCoefficient, productionInjectiveAllowance, Nat.doubleFactorial]

/-! ## Factorial normalization: an exact small-cell warning -/

/-- The order-eight multiplicative subgroup of `ZMod 17`. -/
def smallCellH : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

/-- Unordered two-subset sum profile in the exact `(p,n,r)=(17,8,2)` cell. -/
def smallCellSubsetProfile (y : ZMod 17) : Nat :=
  ((smallCellH.powersetCard 2).filter fun S => (∑ x ∈ S, x) = y).card

/-- Full ordered-pair sum profile in the same cell. -/
def smallCellOrderedProfile (y : ZMod 17) : Nat :=
  ((smallCellH ×ˢ smallCellH).filter fun xy => xy.1 + xy.2 = y).card

/-- The integral numerator `q * sum f_y^2 - (sum f_y)^2` of profile variance. -/
def centeredProfileVariance17 (f : ZMod 17 → Nat) : Nat :=
  17 * ∑ y, (f y) ^ 2 - (∑ y, f y) ^ 2

theorem smallCell_subsetProfile_variance_exact :
    centeredProfileVariance17 smallCellSubsetProfile = 168 := by
  decide

theorem smallCell_orderedProfile_variance_exact :
    centeredProfileVariance17 smallCellOrderedProfile = 392 := by
  decide

/-- Passing from subsets `A` to ordered injective tuples uses `J=2!*A`, so its variance is
multiplied by `(2!)^2=4`. -/
theorem smallCell_scaledSubsetProfile_variance_exact :
    centeredProfileVariance17 (fun y => Nat.factorial 2 * smallCellSubsetProfile y) = 672 := by
  decide

/-- **Factorial-normalization no-go.**  The unscaled subset variance is below the ordered profile
variance (`168 <= 392`), but the BGK-relevant ordered-injective variance is above it
(`672 > 392`).  Thus an unscaled subset-profile comparison cannot close the injective target. -/
theorem smallCell_unscaled_gate_holds_but_orderedInjective_gate_fails :
    centeredProfileVariance17 smallCellSubsetProfile ≤
        centeredProfileVariance17 smallCellOrderedProfile ∧
      centeredProfileVariance17 smallCellOrderedProfile <
        centeredProfileVariance17 (fun y => Nat.factorial 2 * smallCellSubsetProfile y) := by
  decide

/-! ## A finite label quotient that reflects every depth-seven FS11 label -/

/-- Coefficient-vector reduction modulo `29`.  The target is finite for every `m`. -/
def coefficientVectorMod29 (m : Nat) : ℤ[X] →+ (Fin m → ZMod 29) where
  toFun P i := (P.coeff i : ZMod 29)
  map_zero' := by ext i; simp
  map_add' P Q := by ext i; simp

@[simp]
theorem coefficientVectorMod29_apply (m : Nat) (P : ℤ[X]) (i : Fin m) :
    coefficientVectorMod29 m P i = (P.coeff i : ZMod 29) := rfl

/-- Modulo `29` detects every degree-`<m` integer polynomial of coefficient height at most `14`.
The strict inequality `2*14 < 29` is exactly what prevents a false zero. -/
theorem coefficientVectorMod29_eq_zero_imp_eq_zero
    {m : Nat} {P : ℤ[X]} (hdeg : P.natDegree < m)
    (hheight : ∀ i, |P.coeff i| ≤ 14)
    (hmod : coefficientVectorMod29 m P = 0) : P = 0 := by
  ext i
  rw [coeff_zero]
  by_cases hi : i < m
  · let j : Fin m := ⟨i, hi⟩
    have hj := congrFun hmod j
    have hcast : (P.coeff i : ZMod 29) = 0 := by
      simpa [coefficientVectorMod29, j] using hj
    have hdvd : (29 : ℤ) ∣ P.coeff i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (P.coeff i) 29).mp hcast
    exact Int.eq_zero_of_abs_lt_dvd hdvd ((hheight i).trans_lt (by norm_num))
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (not_lt.mp hi))

theorem coefficientVectorMod29_eq_zero_iff
    {m : Nat} {P : ℤ[X]} (hdeg : P.natDegree < m)
    (hheight : ∀ i, |P.coeff i| ≤ 14) :
    coefficientVectorMod29 m P = 0 ↔ P = 0 := by
  constructor
  · exact coefficientVectorMod29_eq_zero_imp_eq_zero hdeg hheight
  · rintro rfl
    simp

/-- The concrete finite quotient reflects zero on every FS11 depth-seven pattern label. -/
theorem depthSevenPattern_coefficientVectorMod29_eq_zero_iff
    {m : Nat} (hm : 0 < m) {a b : Fin 7 → Nat}
    (ha : ∀ i, a i < 2 * m) (hb : ∀ i, b i < 2 * m) :
    coefficientVectorMod29 m (patternPolyG m a b) = 0 ↔
      patternPolyG m a b = 0 := by
  apply coefficientVectorMod29_eq_zero_iff (patternPolyG_natDegree_lt hm ha hb)
  intro i
  simpa using patternPolyG_coeff_abs_le m a b i

/-! ## Exact label-fibre and character-valued sunflower transforms -/

section LabelFibres

variable {alpha : Type*} [AddCommGroup alpha] [DecidableEq alpha]
variable {beta : Type*} [AddCommGroup beta] [DecidableEq beta]

/-- Collisions in one exact signed-label fibre. -/
noncomputable def labelCollisionPairs (G : Finset alpha) (k : Nat)
    (lift : alpha → beta) (c : beta) : Finset (Finset alpha × Finset alpha) :=
  (subsetCollisionPairs G k).filter fun p => signedPairLabel lift p = c

/-- One residual-cardinality stratum in an exact signed-label fibre. -/
noncomputable def labelOverlapStratumPairs (G : Finset alpha) (k r : Nat)
    (lift : alpha → beta) (c : beta) : Finset (Finset alpha × Finset alpha) :=
  (overlapStratumPairs G k r).filter fun p => signedPairLabel lift p = c

/-- Globally disjoint petals in one exact signed-label fibre. -/
noncomputable def labelDisjointCollisionPairs (G : Finset alpha) (r : Nat)
    (lift : alpha → beta) (c : beta) : Finset (Finset alpha × Finset alpha) :=
  (disjointCollisionPairs G r).filter fun p => signedPairLabel lift p = c

noncomputable def labelCompletionFiber (G : Finset alpha) (k r : Nat)
    (lift : alpha → beta) (c : beta) (p : Finset alpha × Finset alpha) :
    Finset (Finset alpha × Finset alpha) :=
  (labelOverlapStratumPairs G k r lift c).filter fun z => residualPair z = p

theorem residualPair_mem_labelDisjointCollisionPairs
    {G : Finset alpha} {k r : Nat} {lift : alpha → beta} {c : beta}
    {z : Finset alpha × Finset alpha}
    (hz : z ∈ labelOverlapStratumPairs G k r lift c) :
    residualPair z ∈ labelDisjointCollisionPairs G r lift c := by
  rw [labelOverlapStratumPairs, Finset.mem_filter] at hz
  rw [labelDisjointCollisionPairs, Finset.mem_filter]
  refine ⟨residualPair_mem_disjointCollisionPairs hz.1, ?_⟩
  rw [signedPairLabel_residualPair]
  exact hz.2

theorem labelCompletionFiber_eq_completionFiber
    (G : Finset alpha) (k r : Nat) (lift : alpha → beta) (c : beta)
    (p : Finset alpha × Finset alpha)
    (hp : p ∈ labelDisjointCollisionPairs G r lift c) :
    labelCompletionFiber G k r lift c p = completionFiber G k r p := by
  rw [labelDisjointCollisionPairs, Finset.mem_filter] at hp
  ext z
  simp only [labelCompletionFiber, labelOverlapStratumPairs, completionFiber,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨hz, _hlabel⟩, hres⟩
    exact ⟨hz, hres⟩
  · rintro ⟨hz, hres⟩
    refine ⟨⟨hz, ?_⟩, hres⟩
    rw [← signedPairLabel_residualPair lift z, hres]
    exact hp.2

theorem card_labelCompletionFiber
    (G : Finset alpha) (k r : Nat) (lift : alpha → beta) (c : beta)
    (p : Finset alpha × Finset alpha)
    (hp : p ∈ labelDisjointCollisionPairs G r lift c) (hrk : r ≤ k) :
    (labelCompletionFiber G k r lift c p).card =
      (G.card - 2 * r).choose (k - r) := by
  rw [labelCompletionFiber_eq_completionFiber G k r lift c p hp]
  exact card_completionFiber G k r p (Finset.mem_filter.mp hp).1 hrk

theorem card_labelOverlapStratumPairs
    (G : Finset alpha) (k r : Nat) (lift : alpha → beta) (c : beta) (hrk : r ≤ k) :
    (labelOverlapStratumPairs G k r lift c).card =
      (labelDisjointCollisionPairs G r lift c).card *
        (G.card - 2 * r).choose (k - r) := by
  classical
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := labelOverlapStratumPairs G k r lift c)
    (t := labelDisjointCollisionPairs G r lift c)
    (f := residualPair)
    (fun z hz => residualPair_mem_labelDisjointCollisionPairs hz)
  rw [hpart]
  calc
    (∑ p ∈ labelDisjointCollisionPairs G r lift c,
        ((labelOverlapStratumPairs G k r lift c).filter
          fun z => residualPair z = p).card) =
        ∑ _p ∈ labelDisjointCollisionPairs G r lift c,
          (G.card - 2 * r).choose (k - r) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact card_labelCompletionFiber G k r lift c p hp hrk
    _ = (labelDisjointCollisionPairs G r lift c).card *
        (G.card - 2 * r).choose (k - r) := by simp

theorem card_labelCollisionPairs_eq_sum_strata
    (G : Finset alpha) (k : Nat) (lift : alpha → beta) (c : beta) :
    (labelCollisionPairs G k lift c).card =
      ∑ r ∈ Finset.range (k + 1),
        (labelOverlapStratumPairs G k r lift c).card := by
  classical
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := labelCollisionPairs G k lift c)
    (t := Finset.range (k + 1))
    (f := fun p => (p.1 \ p.2).card)
    (fun p hp => by
      apply Finset.mem_range.mpr
      have hp' : p ∈ labelCollisionPairs G k lift c := hp
      rw [labelCollisionPairs, Finset.mem_filter] at hp'
      exact Nat.lt_succ_of_le (card_sdiff_le_of_mem_subsetCollisionPairs hp'.1))
  simpa [labelCollisionPairs, labelOverlapStratumPairs, overlapStratumPairs,
    Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hpart

/-- **Coefficientwise sunflower transform.**  Common-core completion preserves the full signed
label, not only the Boolean predicate that it is nonzero. -/
theorem card_labelCollisionPairs_eq_sum_disjoint
    (G : Finset alpha) (k : Nat) (lift : alpha → beta) (c : beta) :
    (labelCollisionPairs G k lift c).card =
      ∑ r ∈ Finset.range (k + 1),
        (labelDisjointCollisionPairs G r lift c).card *
          (G.card - 2 * r).choose (k - r) := by
  rw [card_labelCollisionPairs_eq_sum_strata]
  apply Finset.sum_congr rfl
  intro r hr
  apply card_labelOverlapStratumPairs G k r lift c
  rw [Finset.mem_range] at hr
  omega

section Characters

variable [Fintype beta]
variable {R : Type*} [CommSemiring R]

/-- Character transform of the full label histogram at subset depth `k`. -/
noncomputable def characterCollisionSum (psi : AddChar beta R)
    (G : Finset alpha) (k : Nat) (lift : alpha → beta) : R :=
  ∑ c : beta, ((labelCollisionPairs G k lift c).card : R) * psi c

/-- Character transform of the globally-disjoint label histogram at petal depth `r`. -/
noncomputable def characterDisjointSum (psi : AddChar beta R)
    (G : Finset alpha) (r : Nat) (lift : alpha → beta) : R :=
  ∑ c : beta, ((labelDisjointCollisionPairs G r lift c).card : R) * psi c

/-- **Character-valued sunflower socket.**  Every additive character sees the same triangular
completion transform.  Unlike the nonzero-label census, these coordinates retain signs/phases. -/
theorem characterCollisionSum_eq_sum_disjoint
    (psi : AddChar beta R) (G : Finset alpha) (k : Nat) (lift : alpha → beta) :
    characterCollisionSum psi G k lift =
      ∑ r ∈ Finset.range (k + 1),
        ((G.card - 2 * r).choose (k - r) : R) *
          characterDisjointSum psi G r lift := by
  classical
  unfold characterCollisionSum characterDisjointSum
  simp_rw [card_labelCollisionPairs_eq_sum_disjoint, Nat.cast_sum, Nat.cast_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

end Characters

end LabelFibres

#print axioms nonnegative_onsetThree_correlated_growth
#print axioms lower_rows_do_not_bound_seven
#print axioms pureDepthSevenPolynomial_root_localization
#print axioms primitiveWick_exceeds_allowance_by_exactly_8264
#print axioms smallCell_unscaled_gate_holds_but_orderedInjective_gate_fails
#print axioms depthSevenPattern_coefficientVectorMod29_eq_zero_iff
#print axioms card_labelCollisionPairs_eq_sum_disjoint
#print axioms characterCollisionSum_eq_sum_disjoint

end ArkLib.ProximityGap.Frontier.BGKSunflowerCorrelationNoGo
