/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.FirstPrimeSepticCores
import ArkLib.Research.ProximityGap.Frontier._F1RegionSyzygyInterface
import ArkLib.Research.ProximityGap.Frontier._SYZ66BadCountBridge

/-!
# Rate-1/2 SYZ Strip Audit: F2 Refutation, Master-Hypothesis Vacuity, and 4-Coset F1 No-Go

This module establishes three machine-checked structural results for the rate-`1/2` SYZ proximity
strip assembly (`DOSSIER.md` §3.2, §4.2):

1. **Unconditional refutation of F2 (`SYZ66.StripSyzygyControlledCeiling`) and the `SYZ46–SYZ66`
   census chain on the first prize prime (`ZMod PrizeShapePrimeP30.P`, `n = 2^30`, `k = 2^29`).**
   Monotonicity of `epsMCA` transports `FirstPrimeSepticCores.over_budget` from `313174699 / 2^30`
   to the strip predecessor `357913940 / 2^30`, refuting `SYZ60Dictionary.BadCountCeiling`,
   `SYZ66.StripSyzygyControlledCeiling` (F2), `SYZ57Transport.CountingDictionary`, and
   `SYZ46.StripCensusBound`, and producing an explicit dependent syzygy-carrying stack with
   `2^30 + 1 ≤ mcaBadCount`.
2. **Structural vacuity of `StripMasterHypothesis` (`SYZ40`), `StripMasterHypothesis'` (`SYZ41`),
   and `StripMasterHypothesis''` (`SYZ42`).**
   Instantiating `realizability` / `realizabilityCore` at the admissible upper endpoint `Ucard = n`
   yields `2 * (n - k) + 1 ≤ 2 * (n - k)` via `SYZ20JointRankSuperadditive.union_card_lt_length`,
   proving all three bundled master hypotheses `False` for every `k ≤ n`.
3. **Unconditional refutation of literal `SYZ40.UniformSylvesterInjective` and symbolic 4-coset
   refutation of `SYZ38.SylvesterInjective` and unconditional `ι ≤ 1` on `RegionSyzygyRealizable ∩
   StrictBandCores` at `n = 2^30` on both certified prize primes.**
   Partitioning any cyclic subgroup of order `4 * d` (`4 ≤ d`) into its four `μ_d`-cosets gives
   pairwise-disjoint squarefree vanishing polynomials `X^d - ω^r` (`ω = g^d`) carrying a nonzero
   floor-attained constant syzygy of minimal product-degree `δ₁ = d = max(d, d, d)` (not a
   `SYZ59.middleBand` occupant, so `RegionMiddleExclusion` is not touched), imbalance
   `ι = d / 2 ≥ 2`, strict-band core sizes `2n/3 < 2d + t < 3n/4`, and a nontrivial in-budget
   Sylvester kernel. Instantiated at `d = 2^28`, `t = 178956972` (`2d + t = 715827884`), this
   refutes `SYZ38.SylvesterInjective` and unconditional near-balance `ι ≤ 1` on the region/strict-
   band layer over both `ZMod PrizeShapePrimeP30.P` and `ZMod PrizeShapePrimeP30Second.P`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonSYZMasterAudit

open Finset Polynomial Module
open scoped NNReal ENNReal
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26 (evalCode)
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.Frontier.SYZ46

/-! ## 1. Unconditional refutation of F2 and the `SYZ46–SYZ66` census chain on `P₁` -/

section CensusAndF2Refutation

local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩

/-- The septic-core witness radius `313174699 / 2^30` lies strictly below the strip lattice
predecessor `357913940 / 2^30`. -/
theorem septicRadius_le_stripPredecessor :
    ((313174699 : ℝ≥0) / 2 ^ 30) ≤ predecessorRadius (2 ^ 30) stripNumerator := by
  rw [← NNReal.coe_le_coe, predecessorRadius, show stripNumerator = 357913941 from rfl]
  push_cast
  norm_num

/-- **Over-budget MCA error at the strip predecessor (`357913940 / 2^30 < 1/3`).**
Transporting `FirstPrimeSepticCores.over_budget` upward by `ProximityGap.epsMCA_mono` proves that
the first certified prize field already exceeds `epsStar = 2^-128` at the strip predecessor. -/
theorem epsStar_lt_epsMCA_stripPredecessor :
    (epsStar : ℝ≥0∞) <
      epsMCA (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator) := by
  have hover :
      (epsStar : ℝ≥0∞) <
        epsMCA (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
          ((313174699 : ℝ≥0) / 2 ^ 30) :=
    _root_.ProximityGap.FirstPrimeSepticCores.over_budget
  have hmono :=
    epsMCA_mono (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
      septicRadius_le_stripPredecessor
  exact lt_of_lt_of_le hover hmono

/-- The operational threshold `mcaDeltaStar` on the first certified prize field lies strictly below
the strip floor boundary `357913941 / 2^30 = 1/3 - 1/(3 * 2^30)`. -/
theorem mcaDeltaStar_lt_stripBoundary :
    mcaDeltaStar (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
        (epsStar : ℝ≥0∞) <
      ((stripNumerator : ℕ) : ℝ≥0) / ((2 ^ 30 : ℕ) : ℝ≥0) := by
  refine lt_of_le_of_lt _root_.ProximityGap.FirstPrimeSepticCores.threshold_le ?_
  rw [show stripNumerator = 357913941 from rfl]
  norm_num

/-- **Unconditional refutation of `SYZ60Dictionary.BadCountCeiling`.**
If every word stack had `mcaBadCount ≤ 2^30` at the strip predecessor, `epsMCA_le_of_bad_count_le`
and `2^30 / P₁ ≤ 2^-128` would force `epsMCA ≤ epsStar`, contradicting
`epsStar_lt_epsMCA_stripPredecessor`. -/
theorem not_badCountCeiling : ¬ ArkLib.ProximityGap.Frontier.SYZ60Dictionary.BadCountCeiling := by
  intro hceil
  have hbudget :
      ((2 ^ 30 : ℕ) : ℝ≥0∞) /
          (Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) : ℝ≥0∞) ≤
        (epsStar : ℝ≥0∞) := by
    rw [ZMod.card]
    have hb :=
      natCast_div_le_inv_of_mul_le (E := 2 ^ 30) (Q := 2 ^ 128)
        (p := ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.pos (by norm_num)
    rwa [epsStar_coe_eq_natCast_inv]
  have hle :
      epsMCA (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) stripNumerator) ≤
        (epsStar : ℝ≥0∞) :=
    le_trans
      (epsMCA_le_of_bad_count_le
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator) (2 ^ 30) hceil)
      hbudget
  exact (not_le_of_gt epsStar_lt_epsMCA_stripPredecessor) hle

/-- **Unconditional refutation of F2 (`SYZ66.StripSyzygyControlledCeiling`).**
The isolated dependent-stack ceiling `StripSyzygyControlledCeiling` (`DOSSIER.md` §3.2 F2) implies
`BadCountCeiling` (`SYZ66.badCountCeiling_of_syzygyControlled`) and is therefore `False`. -/
theorem not_stripSyzygyControlledCeiling :
    ¬ ArkLib.ProximityGap.Frontier.SYZ66.StripSyzygyControlledCeiling := fun h =>
  not_badCountCeiling (ArkLib.ProximityGap.Frontier.SYZ66.badCountCeiling_of_syzygyControlled h)

/-- **Unconditional refutation of `SYZ57Transport.CountingDictionary`.** -/
theorem not_countingDictionary :
    ¬ ArkLib.ProximityGap.Frontier.SYZ57Transport.CountingDictionary := fun h =>
  not_badCountCeiling
    (ArkLib.ProximityGap.Frontier.SYZ60Dictionary.badCountCeiling_of_countingDictionary h)

/-- **Unconditional refutation of `SYZ46.StripCensusBound`.** -/
theorem not_stripCensusBound : ¬ StripCensusBound := fun h =>
  not_badCountCeiling (fun u => le_trans (h u) (by norm_num))

/-- **Existence of an over-budget syzygy-carrying stack at the strip predecessor.**
There exists a concrete stack `u` on `ZMod PrizeShapePrimeP30.P` with `2^30 + 1 ≤ mcaBadCount` at
`357913940 / 2^30` whose G87 witness functionals carry an explicit nontrivial syzygy. -/
theorem exists_stripPredecessor_overBudget_syzygy_stack :
    ∃ u : Code.WordStack (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) (Fin 2) (Fin (2 ^ 30)),
      2 ^ 30 + 1 ≤
        mcaBadCount (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) stripNumerator) (u 0) (u 1) ∧
      ∃ φ : Fin 6 × Fin (715827884 - Module.finrank (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
            ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wallCode) →
          Module.Dual (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
            (ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.SyndromePair
              ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wallCode),
        (∀ p,
          φ p (ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.syndromePair
            ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wallCode (u 0) (u 1)) = 0) ∧
        (∀ i, LinearIndependent (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) fun j => φ (i, j)) ∧
        ∃ cc : Fin 6 ×
            Fin (715827884 - Module.finrank (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
              ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wallCode) →
            ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P,
          (∑ p, cc p • φ p = 0) ∧ ∃ p, cc p ≠ 0 := by
  obtain ⟨u, hu⟩ := Classical.not_forall.mp not_badCountCeiling
  have hu' :
      2 ^ 30 + 1 ≤
        mcaBadCount (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) stripNumerator) (u 0) (u 1) :=
    Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_ge hu)
  have h6 :
      6 ≤
        mcaBadCount (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) stripNumerator) (u 0) (u 1) :=
    le_trans (by norm_num) hu'
  exact ⟨u, hu', ArkLib.ProximityGap.Frontier.SYZ66.strip_count_ge_six_forces_syzygy (u 0) (u 1) h6⟩

end CensusAndF2Refutation

/-! ## 2. Structural vacuity of `StripMasterHypothesis`, `'`, and `''` at `Ucard = n` -/

section MasterVacuity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- No `SuperadditiveUnion n k n` configuration exists at the upper endpoint `Ucard = n`:
annihilating a nonzero syndrome vector in a `2(n - k)`-dimensional space forces
`2(n - k) + 1 ≤ 2(n - k)`. -/
theorem not_nonempty_superadditiveUnion_self (n k : ℕ) :
    ¬ Nonempty
        (ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive.SuperadditiveUnion
          (F := K) (V := V) n k n) := by
  rintro ⟨cfg⟩
  have h := ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive.union_card_lt_length cfg
  omega

/-- **`SYZ41.StripMasterHypothesis' K V n k` is `False` whenever `k ≤ n`.** -/
theorem not_stripMasterHypothesis' {n k : ℕ} (hk : k ≤ n) :
    ¬ ArkLib.ProximityGap.SYZ41.StripMasterHypothesis' K V n k := fun H =>
  not_nonempty_superadditiveUnion_self (K := K) (V := V) n k (H.realizability n hk le_rfl)

/-- **`SYZ40.StripMasterHypothesis K V n k` is `False` whenever `k ≤ n`.** -/
theorem not_stripMasterHypothesis {n k : ℕ} (hk : k ≤ n) :
    ¬ ArkLib.ProximityGap.SYZ40.StripMasterHypothesis K V n k := fun H =>
  not_stripMasterHypothesis' hk (ArkLib.ProximityGap.SYZ41.StripMasterHypothesis'.ofSYZ40 H)

/-- **`SYZ42.StripMasterHypothesis'' K V n k` is `False` whenever `k ≤ n`.** -/
theorem not_stripMasterHypothesis'' {n k : ℕ} (hk : k ≤ n) :
    ¬ ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' K V n k := fun H =>
  not_stripMasterHypothesis' hk H.toPrime

end MasterVacuity

/-! ## 3. Literal `UniformSylvesterInjective` refutation and 4-coset on-domain F1 counterexamples -/

section F1Refutations

/-- **Literal `SYZ40.UniformSylvesterInjective K n k` is `False` for `n = 2 * k`, `2 ≤ k`.**
The definition omits pairwise coprimality and squarefreeness of `(WAB, WAC, WBC)`, allowing
`(X^k, X^(k-1), X^(k-1))` with `t = 0` and nonzero constant cofactors `(1, 1)`. -/
theorem not_uniformSylvesterInjective {K : Type*} [Field K] {n k : ℕ}
    (hn : n = 2 * k) (hk : 2 ≤ k) :
    ¬ ArkLib.ProximityGap.SYZ40.UniformSylvesterInjective K n k := by
  intro hU
  have hInj :=
    hU ((Polynomial.X : K[X]) ^ k) ((Polynomial.X : K[X]) ^ (k - 1))
      ((Polynomial.X : K[X]) ^ (k - 1)) k (k - 1) (k - 1) 0
      hn (by omega) (by omega)
      (by rw [natDegree_X_pow, Nat.sub_zero])
      (by rw [natDegree_X_pow, Nat.sub_zero])
      (by rw [natDegree_X_pow, Nat.sub_zero])
      (pow_ne_zero k Polynomial.X_ne_zero)
  have hdiv :
      ((Polynomial.X : K[X]) ^ k) ∣
        ((Polynomial.X : K[X]) ^ (k - 1) * 1 - (Polynomial.X : K[X]) ^ (k - 1) * 1) := by
    rw [sub_self]
    exact dvd_zero _
  have hzero :=
    hInj 1 1 (fun _ => by simp only [natDegree_one, Nat.zero_le])
      (fun _ => by simp only [natDegree_one, Nat.zero_le]) hdiv
  exact one_ne_zero hzero.1

private theorem ne_zero_of_orderOf_pos {K : Type*} [Field K] {g : K} {m : ℕ}
    (hg : orderOf g = m) (hm : 0 < m) : g ≠ 0 := by
  intro h0
  subst h0
  have hfin : ¬ IsOfFinOrder (0 : K) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨t, ht, hpow⟩
    rw [zero_pow ht.ne'] at hpow
    exact zero_ne_one hpow
  have hm0 : m = 0 := hg.symm.trans (orderOf_eq_zero hfin)
  omega

private theorem pow_inj_of_lt_orderOf {K : Type*} [Field K] {g : K} {m i j : ℕ}
    (hg : orderOf g = m) {hi : i < m} {hj : j < m} (heq : g ^ i = g ^ j) :
    i = j := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hg0 : g ≠ 0 := ne_zero_of_orderOf_pos hg hm
  have key : ∀ {a b : ℕ}, a ≤ b → b < m → g ^ a = g ^ b → a = b := by
    intro a b hab hbm hab_eq
    have hmul : g ^ a * 1 = g ^ a * g ^ (b - a) := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]
      exact hab_eq
    have hpow1 : g ^ (b - a) = 1 :=
      (mul_left_cancel₀ (pow_ne_zero a hg0) hmul).symm
    have hdvd : m ∣ b - a := by
      rw [← hg]
      exact orderOf_dvd_iff_pow_eq_one.mpr hpow1
    by_cases hsub : b - a = 0
    · omega
    · have hle : m ≤ b - a := Nat.le_of_dvd (Nat.pos_of_ne_zero hsub) hdvd
      omega
  rcases le_total i j with hij | hji
  · exact key hij hj heq
  · exact (key hji hi heq.symm).symm

/-- The smooth subgroup evaluation domain `{g^i : 0 ≤ i < 4d}` of size `4d`. -/
def cosetDomain {K : Type*} [Field K] [DecidableEq K] (g : K) (d : ℕ) : Finset K :=
  (Finset.range (4 * d)).image (fun i => g ^ i)

/-- The `r`-th `μ_d`-coset `{g^(4j + r) : 0 ≤ j < d}` inside `cosetDomain g d`. -/
def cosetSlice {K : Type*} [Field K] [DecidableEq K] (g : K) (d r : ℕ) : Finset K :=
  (Finset.range d).image (fun j => g ^ (4 * j + r))

theorem card_cosetDomain {K : Type*} [Field K] [DecidableEq K] {g : K} {d : ℕ}
    (hg : orderOf g = 4 * d) :
    (cosetDomain g d).card = 4 * d := by
  unfold cosetDomain
  have hinj : Set.InjOn (fun i => g ^ i) (Finset.range (4 * d) : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    exact pow_inj_of_lt_orderOf hg (hi := hi) (hj := hj) hij
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

theorem card_cosetSlice {K : Type*} [Field K] [DecidableEq K] {g : K} {d r : ℕ}
    (hg : orderOf g = 4 * d) (hr : r < 4) :
    (cosetSlice g d r).card = d := by
  unfold cosetSlice
  have hinj : Set.InjOn (fun j => g ^ (4 * j + r)) (Finset.range d : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    have heq : 4 * i + r = 4 * j + r :=
      pow_inj_of_lt_orderOf hg (hi := by omega) (hj := by omega) hij
    omega
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

theorem cosetSlice_subset_cosetDomain {K : Type*} [Field K] [DecidableEq K]
    (g : K) (d : ℕ) {r : ℕ} (hr : r < 4) :
    cosetSlice g d r ⊆ cosetDomain g d := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  rw [Finset.mem_range] at hj
  exact Finset.mem_image.mpr ⟨4 * j + r, Finset.mem_range.mpr (by omega), rfl⟩

theorem disjoint_cosetSlice {K : Type*} [Field K] [DecidableEq K] {g : K} {d r₁ r₂ : ℕ}
    (hg : orderOf g = 4 * d) (hr₁ : r₁ < 4) (hr₂ : r₂ < 4) (hne : r₁ ≠ r₂) :
    Disjoint (cosetSlice g d r₁) (cosetSlice g d r₂) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx₁ hx₂
  rcases Finset.mem_image.mp hx₁ with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hx₂ with ⟨j, hj, hij⟩
  rw [Finset.mem_range] at hi hj
  have heq : 4 * i + r₁ = 4 * j + r₂ :=
    pow_inj_of_lt_orderOf hg (hi := by omega) (hj := by omega) hij.symm
  omega

/-- **Exact vanishing polynomial of each `μ_d`-coset:**
`∏ x ∈ cosetSlice g d r, (X - C x) = X^d - C ((g^d)^r)`. -/
theorem vanishing_cosetSlice {K : Type*} [Field K] [DecidableEq K] {g : K} {d r : ℕ}
    (hg : orderOf g = 4 * d) (hd : 1 ≤ d) (hr : r < 4) :
    ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d r) =
      Polynomial.X ^ d - C ((g ^ d) ^ r) := by
  set S := cosetSlice g d r
  set P : K[X] := ArkLib.ProximityGap.F1RegionSyzygy.vanishing S
  set Q : K[X] := Polynomial.X ^ d - C ((g ^ d) ^ r)
  have hcard : S.card = d := card_cosetSlice hg hr
  have hPm : P.Monic := ArkLib.ProximityGap.F1RegionSyzygy.vanishing_monic S
  have hPd : P.natDegree = d :=
    (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_natDegree S).trans hcard
  have hPtop : P.coeff d = 1 := by
    rw [← hPd, Polynomial.coeff_natDegree]
    exact hPm.leadingCoeff
  have hXtop : ((Polynomial.X : K[X]) ^ d).coeff d = 1 := by
    have hXm : ((Polynomial.X : K[X]) ^ d).Monic := Polynomial.monic_X.pow d
    have hl : ((Polynomial.X : K[X]) ^ d).leadingCoeff = 1 := hXm.leadingCoeff
    rwa [← Polynomial.coeff_natDegree, Polynomial.natDegree_X_pow] at hl
  have hC0 : ∀ m : ℕ, 1 ≤ m → (C ((g ^ d) ^ r) : K[X]).coeff m = 0 := fun m hm =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_C]; omega)
  have hdeg : (P - Q).degree < (S.card : WithBot ℕ) := by
    rw [hcard, Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rcases eq_or_lt_of_le hm with rfl | hgt
    · dsimp only [Q]
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, hPtop, hXtop, hC0 d hd]
      ring
    · have hPm0 : P.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hXm0 : ((Polynomial.X : K[X]) ^ d).coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_X_pow]; exact hgt)
      dsimp only [Q]
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, hPm0, hXm0, hC0 m (by omega)]
      ring
  have heval : ∀ x ∈ S, (P - Q).eval x = 0 := by
    intro x hx
    have hPx : P.eval x = 0 := by
      simp only [P, ArkLib.ProximityGap.F1RegionSyzygy.vanishing, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hx
        (by simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    have hg4d : g ^ (4 * d) = 1 := by
      rw [← hg]
      exact pow_orderOf_eq_one g
    have hxd : (g ^ (4 * j + r)) ^ d = (g ^ d) ^ r := by
      have hexp : (4 * j + r) * d = 4 * d * j + d * r := by ring
      rw [← pow_mul, hexp, pow_add, pow_mul, hg4d, one_pow, one_mul, pow_mul]
    have hQx : Q.eval (g ^ (4 * j + r)) = 0 := by
      simp only [Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, hxd, sub_self]
    rw [Polynomial.eval_sub, hPx, hQx, sub_self]
  exact sub_eq_zero.mp
    (Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (f := P - Q) (s := S) hdeg heval)

private theorem fourCoset_const_syzygy {K : Type*} [Field K] [DecidableEq K] {g : K} {d : ℕ}
    (hg : orderOf g = 4 * d) (hd : 1 ≤ d) :
    ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 0) * C (g ^ d - (g ^ d) ^ 2) +
      ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 1) * C ((g ^ d) ^ 2 - 1) +
      ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 2) * C (1 - g ^ d) = 0 := by
  rw [vanishing_cosetSlice hg hd (by norm_num),
    vanishing_cosetSlice hg hd (by norm_num),
    vanishing_cosetSlice hg hd (by norm_num)]
  simp only [pow_zero, pow_one, map_sub, map_one]
  ring

private theorem fourCoset_cofactor_ne_zero {K : Type*} [Field K] {g : K} {d : ℕ}
    (hg : orderOf g = 4 * d) (hd : 1 ≤ d) :
    g ^ d - (g ^ d) ^ 2 ≠ 0 ∧ (g ^ d) ^ 2 - 1 ≠ 0 ∧ 1 - g ^ d ≠ 0 := by
  refine ⟨sub_ne_zero.mpr ?_, sub_ne_zero.mpr ?_, sub_ne_zero.mpr ?_⟩
  · intro heq
    have hpow : g ^ d = g ^ (2 * d) := by
      calc g ^ d = (g ^ d) ^ 2 := heq
        _ = g ^ (d * 2) := (pow_mul g d 2).symm
        _ = g ^ (2 * d) := by ring_nf
    have hidx := pow_inj_of_lt_orderOf hg (hi := by omega) (hj := by omega) hpow
    omega
  · intro heq
    have hpow : g ^ (2 * d) = g ^ 0 := by
      calc g ^ (2 * d) = g ^ (d * 2) := by ring_nf
        _ = (g ^ d) ^ 2 := pow_mul g d 2
        _ = 1 := heq
        _ = g ^ 0 := (pow_zero g).symm
    have hidx := pow_inj_of_lt_orderOf hg (hi := by omega) (hj := by omega) hpow
    omega
  · intro heq
    have hpow : g ^ 0 = g ^ d := by
      rw [pow_zero]
      exact heq
    have hidx := pow_inj_of_lt_orderOf hg (hi := by omega) (hj := by omega) hpow
    omega

/-- The first three `μ_d`-cosets have exact minimal syzygy product-degree `δ₁ = d`. -/
theorem fourCoset_minimalSyzygyDegree {K : Type*} [Field K] [DecidableEq K] {g : K} {d : ℕ}
    (hg : orderOf g = 4 * d) (hd : 1 ≤ d) :
    ArkLib.ProximityGap.F1RegionSyzygy.MinimalSyzygyDegree
      (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 0))
      (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 1))
      (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 2)) d := by
  have hcof := fourCoset_cofactor_ne_zero hg hd
  have hdeg0 : (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 0)).natDegree = d :=
    (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_natDegree _).trans
      (card_cosetSlice hg (by norm_num))
  have hdeg1 : (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 1)).natDegree = d :=
    (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_natDegree _).trans
      (card_cosetSlice hg (by norm_num))
  have hdeg2 : (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 2)).natDegree = d :=
    (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_natDegree _).trans
      (card_cosetSlice hg (by norm_num))
  constructor
  · refine ⟨C (g ^ d - (g ^ d) ^ 2), C ((g ^ d) ^ 2 - 1), C (1 - g ^ d),
      fourCoset_const_syzygy hg hd, ?_, ?_, ?_, ?_⟩
    · rintro ⟨h0, _, _⟩
      exact hcof.1 (C_eq_zero.mp h0)
    · exact natDegree_mul_le.trans (by rw [hdeg0, natDegree_C]; omega)
    · exact natDegree_mul_le.trans (by rw [hdeg1, natDegree_C]; omega)
    · exact natDegree_mul_le.trans (by rw [hdeg2, natDegree_C]; omega)
  · intro δ hsyz
    obtain ⟨sAB, sAC, sBC, hrel, hnz, hAB, hAC, hBC⟩ := hsyz
    have hfloor :=
      ArkLib.ProximityGap.SYZ47.syzygy_product_degree_ge_max
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 0))
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 1))
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 2))
        sAB sAC sBC δ
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_isCoprime
          (disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num)))
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_isCoprime
          (disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num)))
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_isCoprime
          (disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num)))
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_ne_zero _)
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_ne_zero _)
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing_ne_zero _)
        (by rw [hdeg0, hdeg1, hdeg2]; omega)
        (by rw [hdeg0, hdeg1, hdeg2]; omega)
        (by rw [hdeg0, hdeg1, hdeg2]; omega)
        hrel hnz hAB hAC hBC
    rw [hdeg0, hdeg1, hdeg2] at hfloor
    omega

/-- **Symbolic 4-coset `RegionSyzygyRealizable` theorem.**
Over any field `K` containing an element `g` of order `4 * d` (`4 ≤ d`), every triple-region size
`t` in `[⌈(2d + 1)/3⌉, d - 1]` produces an explicit on-domain `RegionSyzygyRealizable K d d d t
(2 * d) d` witness on `cosetDomain g d`. -/
theorem fourCoset_regionSyzygyRealizable {K : Type*} [Field K] [DecidableEq K]
    {g : K} {d t : ℕ} (hg : orderOf g = 4 * d) (hd : 4 ≤ d)
    (ht_lo : 2 * d + 1 ≤ 3 * t) (ht_hi : t ≤ d - 1) :
    ArkLib.ProximityGap.F1RegionSyzygy.RegionSyzygyRealizable K d d d t (2 * d) d := by
  have ht_le : t ≤ (cosetSlice g d 3).card := by
    rw [card_cosetSlice hg (by norm_num)]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq ht_le
  refine ⟨cosetDomain g d, cosetSlice g d 0, cosetSlice g d 1, cosetSlice g d 2, T,
    ?_, ?_, fourCoset_minimalSyzygyDegree hg (by omega)⟩
  · refine ⟨?_, ?_,
      cosetSlice_subset_cosetDomain g d (by norm_num),
      cosetSlice_subset_cosetDomain g d (by norm_num),
      cosetSlice_subset_cosetDomain g d (by norm_num),
      hTsub.trans (cosetSlice_subset_cosetDomain g d (by norm_num)),
      disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num),
      disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num),
      Disjoint.mono_right hTsub (disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num)),
      disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num),
      Disjoint.mono_right hTsub (disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num)),
      Disjoint.mono_right hTsub (disjoint_cosetSlice hg (by norm_num) (by norm_num) (by norm_num)),
      card_cosetSlice hg (by norm_num),
      card_cosetSlice hg (by norm_num),
      card_cosetSlice hg (by norm_num),
      hTcard⟩
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      have hg4d : g ^ (4 * d) = 1 := by
        rw [← hg]
        exact pow_orderOf_eq_one g
      have hexp : i * (2 * (2 * d)) = 4 * d * i := by ring
      rw [← pow_mul, hexp, pow_mul, hg4d, one_pow]
    · rw [card_cosetDomain hg]
      ring
  · refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Every 4-coset witness in the strip band `[⌈(2d + 1)/3⌉, d - 1]` satisfies
`SYZ50.StrictBandCores d d d t (2 * d)` (`pA = pB = pC = 0`, `2n/3 < 2d + t < 3n/4`) and
`SYZ48.BalancedInterior d d d`, with Hilbert–Burch imbalance `ι = d / 2 ≥ 2`. -/
theorem fourCoset_strictBandCores_and_imbalance {d t : ℕ}
    (hd : 4 ≤ d) (ht_lo : 2 * d + 1 ≤ 3 * t) (ht_hi : t ≤ d - 1) :
    ArkLib.ProximityGap.SYZ50.StrictBandCores d d d t (2 * d) ∧
      ArkLib.ProximityGap.SYZ48.BalancedInterior d d d ∧
      ArkLib.ProximityGap.SYZ45.imbalance d d d d = d / 2 ∧
      2 ≤ ArkLib.ProximityGap.SYZ45.imbalance d d d d := by
  refine ⟨⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, 0, 0, 0, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · unfold ArkLib.ProximityGap.SYZ48.BalancedInterior
    omega
  · unfold ArkLib.ProximityGap.SYZ45.imbalance
    omega
  · unfold ArkLib.ProximityGap.SYZ45.imbalance
    omega

/-- **Failure of `SYZ38.SylvesterInjective` on the 4-coset vanishing triple.**
The constant cofactors `(-((g^d)^2 - 1), 1 - g^d)` have degree `0 ≤ 2d - 1 - (d + t)` and lie in
the kernel of the generalized Sylvester map modulo `vanishing (cosetSlice g d 0)`. -/
theorem fourCoset_not_sylvesterInjective {K : Type*} [Field K] [DecidableEq K]
    {g : K} {d t : ℕ} (hg : orderOf g = 4 * d) (hd : 4 ≤ d) (_ht_hi : t ≤ d - 1) :
    ¬ ArkLib.ProximityGap.SYZ38.SylvesterInjective
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 0))
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 1))
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 2))
        (2 * d - 1 - (d + t)) (2 * d - 1 - (d + t)) := by
  intro hInj
  have hcof := fourCoset_cofactor_ne_zero hg (by omega)
  have hsyz := fourCoset_const_syzygy hg (by omega)
  set rAC : K[X] := C (-((g ^ d) ^ 2 - 1))
  set rBC : K[X] := C (1 - g ^ d)
  have hdvd :
      ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 0) ∣
        (ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 1) * rAC -
          ArkLib.ProximityGap.F1RegionSyzygy.vanishing (cosetSlice g d 2) * rBC) := by
    refine ⟨C (g ^ d - (g ^ d) ^ 2), ?_⟩
    simp only [rAC, rBC, map_neg]
    linear_combination -hsyz
  have hzero :=
    hInj rAC rBC
      (fun _ => by simp only [rAC, natDegree_C, Nat.zero_le])
      (fun _ => by simp only [rBC, natDegree_C, Nat.zero_le])
      hdvd
  exact (neg_ne_zero.mpr hcof.2.1) (C_eq_zero.mp hzero.1)

/-- **Production `n = 2^30` region-layer F1 witness on the FIRST certified prize prime.**
At `d = 2^28`, `t = 178956972`, `k = 2^29`, `n = 2^30` (exact strip core size
`2d + t = 715827884`), `ZMod PrizeShapePrimeP30.P` hosts a pairwise-coprime squarefree `μ_{2^30}`
witness with `StrictBandCores`, `ι = 2^27 = 134217728`, and `¬ SylvesterInjective`. -/
theorem firstPrime_strip_fourCoset_witness :
    letI : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
      ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩
    ArkLib.ProximityGap.F1RegionSyzygy.RegionSyzygyRealizable
        (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) (2 ^ 28) (2 ^ 28) (2 ^ 28)
        178956972 (2 ^ 29) (2 ^ 28) ∧
      ArkLib.ProximityGap.SYZ50.StrictBandCores (2 ^ 28) (2 ^ 28) (2 ^ 28) 178956972 (2 ^ 29) ∧
      ArkLib.ProximityGap.SYZ45.imbalance (2 ^ 28) (2 ^ 28) (2 ^ 28) (2 ^ 28) = 2 ^ 27 ∧
      ¬ ArkLib.ProximityGap.SYZ38.SylvesterInjective
          (ArkLib.ProximityGap.F1RegionSyzygy.vanishing
            (cosetSlice ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 28) 0))
          (ArkLib.ProximityGap.F1RegionSyzygy.vanishing
            (cosetSlice ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 28) 1))
          (ArkLib.ProximityGap.F1RegionSyzygy.vanishing
            (cosetSlice ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 28) 2))
          (2 ^ 29 - 1 - (2 ^ 28 + 178956972)) (2 ^ 29 - 1 - (2 ^ 28 + 178956972)) := by
  have : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
    ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩
  have hg : orderOf ArkLib.ProximityGap.PrizeShapePrimeP30.g = 4 * 2 ^ 28 := by
    rw [ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g]
    norm_num
  have hk : 2 * 2 ^ 28 = 2 ^ 29 := by norm_num
  have hreg :=
    fourCoset_regionSyzygyRealizable (t := 178956972) hg (by norm_num) (by norm_num) (by norm_num)
  have hsbc :=
    fourCoset_strictBandCores_and_imbalance (d := 2 ^ 28) (t := 178956972)
      (by norm_num) (by norm_num) (by norm_num)
  have hnsylv :=
    fourCoset_not_sylvesterInjective (t := 178956972) hg (by norm_num) (by norm_num)
  rw [hk] at hreg hsbc hnsylv
  refine ⟨hreg, hsbc.1, ?_, hnsylv⟩
  rw [hsbc.2.2.1]
  norm_num

/-- **Production `n = 2^30` region-layer F1 witness on the SECOND certified prize prime.**
Identical `d = 2^28`, `t = 178956972`, `k = 2^29`, `n = 2^30` certificate over
`ZMod PrizeShapePrimeP30Second.P`. -/
theorem secondPrime_strip_fourCoset_witness :
    letI : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
      ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩
    ArkLib.ProximityGap.F1RegionSyzygy.RegionSyzygyRealizable
        (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) (2 ^ 28) (2 ^ 28) (2 ^ 28)
        178956972 (2 ^ 29) (2 ^ 28) ∧
      ArkLib.ProximityGap.SYZ50.StrictBandCores (2 ^ 28) (2 ^ 28) (2 ^ 28) 178956972 (2 ^ 29) ∧
      ArkLib.ProximityGap.SYZ45.imbalance (2 ^ 28) (2 ^ 28) (2 ^ 28) (2 ^ 28) = 2 ^ 27 ∧
      ¬ ArkLib.ProximityGap.SYZ38.SylvesterInjective
          (ArkLib.ProximityGap.F1RegionSyzygy.vanishing
            (cosetSlice ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2 ^ 28) 0))
          (ArkLib.ProximityGap.F1RegionSyzygy.vanishing
            (cosetSlice ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2 ^ 28) 1))
          (ArkLib.ProximityGap.F1RegionSyzygy.vanishing
            (cosetSlice ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2 ^ 28) 2))
          (2 ^ 29 - 1 - (2 ^ 28 + 178956972)) (2 ^ 29 - 1 - (2 ^ 28 + 178956972)) := by
  have : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
    ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩
  have hg : orderOf ArkLib.ProximityGap.PrizeShapePrimeP30Second.g = 4 * 2 ^ 28 := by
    rw [ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g]
    norm_num
  have hk : 2 * 2 ^ 28 = 2 ^ 29 := by norm_num
  have hreg :=
    fourCoset_regionSyzygyRealizable (t := 178956972) hg (by norm_num) (by norm_num) (by norm_num)
  have hsbc :=
    fourCoset_strictBandCores_and_imbalance (d := 2 ^ 28) (t := 178956972)
      (by norm_num) (by norm_num) (by norm_num)
  have hnsylv :=
    fourCoset_not_sylvesterInjective (t := 178956972) hg (by norm_num) (by norm_num)
  rw [hk] at hreg hsbc hnsylv
  refine ⟨hreg, hsbc.1, ?_, hnsylv⟩
  rw [hsbc.2.2.1]
  norm_num

end F1Refutations

#print axioms epsStar_lt_epsMCA_stripPredecessor
#print axioms mcaDeltaStar_lt_stripBoundary
#print axioms not_badCountCeiling
#print axioms not_stripSyzygyControlledCeiling
#print axioms not_countingDictionary
#print axioms not_stripCensusBound
#print axioms exists_stripPredecessor_overBudget_syzygy_stack
#print axioms not_stripMasterHypothesis
#print axioms not_stripMasterHypothesis'
#print axioms not_stripMasterHypothesis''
#print axioms not_uniformSylvesterInjective
#print axioms vanishing_cosetSlice
#print axioms fourCoset_regionSyzygyRealizable
#print axioms fourCoset_strictBandCores_and_imbalance
#print axioms fourCoset_not_sylvesterInjective
#print axioms firstPrime_strip_fourCoset_witness
#print axioms secondPrime_strip_fourCoset_witness

end ArkLib.ProximityGap.Frontier.CarbonSYZMasterAudit
