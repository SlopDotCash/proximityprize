/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LocatorShortening
import ArkLib.Research.ProximityGap.Frontier.TerminalDimensionThreshold

/-! # Sharp MCA thresholds on shortened evaluation domains

Extending a shorter received pair to length 2^30 preserves every bad scalar at
the same integer error count and increases the code dimension by the number of
new coordinates. The three-head attack at the threshold can instead be built
on the original shorter domain.
-/
set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.ShortenedThreeHeadThreshold
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m K B p : ℕ}

private theorem predecessor_long [CharP F p] (D : Fin n ↪ F) (hp : 1744830589 < p)
    (hB : Fintype.card F / 2^128 = B) (hl : 1565873494 ≤ B) (hu : B ≤ 2147483648) :
    let e := max 671088640 (B/3)
    epsMCA (F := F) (ReedSolomon.code D k : Set (Fin n → F)) (((e-1 : ℕ) : ℝ≥0)/n) ≤
      tolerance := by
  dsimp only
  by_cases h : B ≤ 2013265922
  · rw [max_eq_left (by omega : B/3 ≤ 671088640)]
    have safe := (FiveEighthsPlateauThreshold.classification D (Fintype.card_fin _) hp
      (by omega) (by omega) 1).2 (((671088640-1 : ℕ) : ℝ≥0)/n)
    rw [epsMCA_interleaved_eq] at safe
    exact safe.mpr (by norm_num [n])
  · rw [max_eq_right (by omega : 671088640 ≤ B/3)]
    have safe := (UniversalCubicBudgetWindow.classification D (Fintype.card_fin _) hp hB
      (by omega) hu 1).2 (((B/3-1 : ℕ) : ℝ≥0)/n)
    rw [epsMCA_interleaved_eq] at safe
    apply safe.mpr
    apply (div_lt_div_iff_of_pos_right (by norm_num [n] : (0:ℝ≥0)<n)).mpr
    exact_mod_cast (show B/3-1 < B/3 by omega)

/-- Exact first-failure count at every covered length and dimension. The last
packing hypothesis allows the exceptional three-head construction at dimension
at least three and the ordinary construction at dimension two. -/
theorem classification [NeZero m] [CharP F p] (dom : Fin m ↪ F) (hp : 1744830589 < p)
    (hB : Fintype.card F / 2^128 = B) (hl : 1565873494 ≤ B) (hu : B ≤ 2147483648)
    (hm : m ≤ n) (hk : 2 ≤ K) (hK : K + (n-m) ≤ k)
    (hfit : 2*m ≤ 3*(max 671088640 (B/3))+2*K)
    (hpair : 3 ≤ K ∨ 2*m ≤ 3*(max 671088640 (B/3))+3)
    (width : ℕ) [NeZero width] :
    let e := max 671088640 (B/3)
    let t : ℝ≥0 := (e : ℝ≥0)/m
    mcaDeltaStar (F := F) ((ReedSolomon.code dom K : Set (Fin m → F)) ^⋈ (Fin width)) tolerance = t ∧
      ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code dom K : Set (Fin m → F)) ^⋈ (Fin width)) δ ≤
        tolerance ↔ δ < t := by
  classical
  let e := max 671088640 (B/3)
  change 2*m ≤ 3*e+2*K at hfit
  change 3 ≤ K ∨ 2*m ≤ 3*e+3 at hpair
  have he : 671088640 ≤ e := le_max_left ..
  have heu : e ≤ 715827882 := by dsimp [e]; omega
  have hfield : n ≤ Fintype.card F := by dsimp [n]; omega
  have hmlo : 1006632962 ≤ m := by dsimp [n,k] at hm hK; omega
  have ht : K < m-e := by dsimp [k] at hK; omega
  let pred : ℝ≥0 := ((e-1 : ℕ) : ℝ≥0)/n
  let t : ℝ≥0 := (e : ℝ≥0)/m
  obtain ⟨old,D,hrestrict⟩ := LocatorShortening.exists_extended_domain dom hm hfield
  have transfer := LocatorShortening.eps_le_extension old D (by omega : 0<K) (e-1)
  rw [hrestrict] at transfer
  have htlong : k < ⌈(1-pred)*(Fintype.card (Fin n) : ℝ≥0)⌉₊ := by
    rw [Fintype.card_fin]
    dsimp only [pred]
    rw [LocatorShortening.agreement_mass, Nat.ceil_natCast]
    dsimp [k,n]
    omega
  have safe := transfer.trans ((DimensionRaiseMCA.eps_mono_dimension D (by omega) hK pred htlong).trans
    (predecessor_long D hp hB hl hu))
  have size : (1-t)*(m : ℝ≥0) ≤ ((m-e : ℕ) : ℝ≥0) := (LocatorShortening.agreement_mass m e).le
  have field_bound : Fintype.card F ≤ 2^256 := by omega
  have budget : Fintype.card F/2^128 < 3*(e+1) := by dsimp [e]; omega
  have count : m-(m-e)=e := by omega
  have bad : tolerance < epsMCA (F := F) (ReedSolomon.code dom K : Set (Fin m → F)) t := by
    rcases hpair with hthree | htwo
    · apply ExceptionalHeadLocatorMass.over_budget_128 (m := 3) (t := m-e) dom t
        (by decide) hthree ht (Nat.sub_le ..) (by omega) size field_bound
      rwa [count]
    · apply ManyHeadLocatorMass.over_budget_128 (h := 0) (d := 2) (r := m-e-1) dom t
        (by omega) hk (by omega) (by simpa only [show 0+(m-e-1)+1=m-e by omega] using size) field_bound
      simpa only [show m-(0+(m-e-1))=e+1 by omega] using budget
  have exact_threshold := MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
    (a := e) (by omega) (by omega) _ _ safe bad
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact exact_threshold, ?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! above
    exact bad.not_ge ((epsMCA_mono _ above).trans good)
  · intro below
    by_contra! failure
    have bound := mcaDeltaStar_le_of_bad _ _ failure
    rw [exact_threshold] at bound
    exact below.not_ge bound

section Named
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
local instance : Fact P.Prime := ⟨prime_P⟩

/-- On the second designated prime the first count is constant across
67,108,863 consecutive lengths, at every dimension from two through the
shortened maximum and every positive width. -/
theorem second_prime [NeZero m] (dom : Fin m ↪ ZMod P) (hm : m ≤ 1073741824)
    (hk : 2 ≤ K) (hK : K + (1073741824-m) ≤ 67108864) (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := 715827882/(m : ℝ≥0)
    mcaDeltaStar (F := ZMod P) ((ReedSolomon.code dom K : Set (Fin m → ZMod P)) ^⋈ (Fin width))
      tolerance = t ∧ ∀ δ : ℝ≥0, epsMCA (F := ZMod P)
      ((ReedSolomon.code dom K : Set (Fin m → ZMod P)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ < t := by
  exact classification dom (p := P) (B := 2147483648) (by decide) (by rw [ZMod.card]; decide)
    (by decide) (by decide) hm hk hK (by omega) (.inr (by omega)) width
end Named

#print axioms classification
#print axioms second_prime
end ArkLib.ProximityGap.Frontier.ShortenedThreeHeadThreshold
