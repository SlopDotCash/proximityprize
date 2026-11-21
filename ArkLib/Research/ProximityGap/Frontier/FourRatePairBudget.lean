/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.RateQuarterPairOverlap
import ArkLib.Research.ProximityGap.Frontier.RateHalfApolarBudget
import ArkLib.Research.ProximityGap.Frontier._TwoCorePackingThreshold
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction

/-! # The exact four-rate MCA threshold on a field-budget interval -/

set_option autoImplicit false
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.FourRatePairBudget

abbrev n : ℕ := 1073741824
abbrev upperBudget : ℕ := 181823221
noncomputable abbrev code {p : ℕ} [Fact p.Prime] (g : ZMod p) (k : ℕ) :=
  evalCode g n (k - 1)

private theorem pair_gap {e k : ℕ} (he : e < upperBudget) (hk : k ≤ 536870912) :
    n*(16*n+16*15*(e+(k-1))) < (16*(n-e))^2 := by
  have hc : e+(k-1) ≤ 718694131 := by dsimp [upperBudget] at he; omega
  have ht : 16*891918604 ≤ 16*(n-e) := by dsimp [n,upperBudget] at *; omega
  calc
    _ ≤ n*(16*n+16*15*718694131) := Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ hc) _)
    _ < (16*891918604)^2 := by decide
    _ ≤ _ := Nat.pow_le_pow_left ht 2

/-- The agreement-set pair bound and the staircase at the first fourteen steps
control every received pair up to the stated maximum Hamming count. -/
theorem count_upper {p k e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = n) (hk : 1 ≤ k) (hmax : k ≤ 536870912) (he : e < upperBudget) :
    epsMCA (F := ZMod p) (code g k) ((e : ℝ≥0) / n) ≤
      ((e+1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  let δ : ℝ≥0 := (e : ℝ≥0) / n
  let dom := KKH26RegimeSplit.powDomain g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
  by_cases small : e < 14
  · rw [code, Ownership.evalCode_pred_eq_rsCode hg hk]
    conv_rhs => rw [← ZMod.card p]
    exact SpikeFloor.epsMCA_le_j_div_card _
      (SpikeFloor.rsCode_noWeightLE _ (by dsimp [n]; omega))
      (by simp [Fintype.card_fin, n, Nat.cast_add_one])
  have hcode : code g k = (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    simpa only [code, dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg) (k-1)
  rw [hcode]
  refine (epsMCA_le_of_badCount_le _ _ (e+1) ?_).trans (by rw [ZMod.card])
  intro u
  have hen : e ≤ n := by dsimp [n,upperBudget] at *; omega
  have hn : e + (n-e) = n := by omega
  have hf := RateQuarterPairOverlap.family_card_of_pair_mass
    (canonicalBadScalarRichPointFamily dom (k := k) δ u hk) (e := e) (t := n-e)
    ((Fintype.card_fin _).trans hn.symm) hk (by omega)
    (TwoCorePackingThreshold.agreement_ceiling e hen) (by rw [hn]; exact pair_gap he hmax)
  simpa only [canonicalBadScalarRichPointFamily,badScalars,δ] using hf

/-- The universal spike realizes at least e+1 numerator at all steps needed here. -/
theorem count_lower {p k e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = n) (hk : 1 ≤ k) (hmax : k ≤ 536870912) (he : e ≤ upperBudget) :
    ((e+1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ epsMCA (F := ZMod p) (code g k) ((e : ℝ≥0) / n) := by
  let dom := Ownership.smoothDom g n hg
  have hroom : e+1+k ≤ n := by dsimp [n,upperBudget] at *; omega
  let positions : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
  rw [code, Ownership.evalCode_pred_eq_rsCode hg hk]
  conv_lhs => rw [← ZMod.card p]
  exact SpikeFloor.epsMCA_ge_j_div_card (SpikeFloor.rsCode dom k)
    (SpikeFloor.rsCode_noWeightLE dom hroom)
    (by simp [Fintype.card_fin, n]) (by omega) (by rw [Fintype.card_fin]; omega)
    positions (positions.trans dom) (b := (1 : ZMod p)) one_ne_zero

/-- The exact MCA numerator at every error count below the upper budget. -/
theorem exact_mass {p k e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = n) (hk : 1 ≤ k) (hmax : k ≤ 536870912) (he : e < upperBudget) :
    epsMCA (F := ZMod p) (code g k) ((e : ℝ≥0) / n) =
      ((e+1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) :=
  le_antisymm (count_upper hg hk hmax he) (count_lower hg hk hmax he.le)

/-- Every prime in the budget interval and every dimension through rate one half
has an operational threshold exactly equal to the rounded budget divided by length. -/
theorem threshold {p k B : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 1 ≤ k) (hmax : k ≤ 536870912) (hB : B = p / 2^128)
    (hpos : 1 ≤ B) (hlim : B ≤ upperBudget) :
    mcaDeltaStar (F := ZMod p) (code g k) (epsStar : ℝ≥0∞) = (B : ℝ≥0) / n := by
  rw [epsStar_coe_eq_natCast_inv]
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad
    apply lt_of_lt_of_le _ (count_lower hg hk hmax hlim)
    have hp : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl (ENNReal.natCast_ne_top p)),
      ← ENNReal.div_eq_inv_mul,
      ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _))]
    exact_mod_cast (by simpa only [hB, Nat.mul_comm] using
      Nat.lt_mul_div_succ p (by decide : 0 < 2^128))
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good hpos
      (by dsimp [n,upperBudget] at *; omega : B ≤ n)
    rw [predecessorRadius, exact_mass hg hk hmax (by omega), Nat.sub_add_cancel hpos]
    exact natCast_div_le_inv_of_mul_le (Q := 2^128) (by decide) (Fact.out (p := p.Prime)).pos
      (hB ▸ Nat.div_mul_le_self ..)

/-- All positive interleaving widths and all real radii have the same strict cutoff. -/
theorem interleaved_good_iff {p k B : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 1 ≤ k) (hmax : k ≤ 536870912) (hB : B = p / 2^128) (hpos : 1 ≤ B)
    (hlim : B ≤ upperBudget) (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := ZMod p) (A := Fin width → ZMod p) ((code g k) ^⋈ (Fin width)) δ ≤
      (epsStar : ℝ≥0∞) ↔ δ < (B : ℝ≥0) / n := by
  have hc := Ownership.evalCode_pred_eq_rsCode hg hk
  unfold code
  rw [hc, epsMCA_interleaved_eq, ← hc]
  have exactRadius := threshold hg hk hmax hB hpos hlim
  have hlt : mcaDeltaStar (F := ZMod p) (code g k) (epsStar : ℝ≥0∞) < 1 := by
    rw [exactRadius, div_lt_one (by norm_num [n])]
    exact_mod_cast (show B<n by dsimp [n,upperBudget] at *; omega)
  rw [← exactRadius]
  constructor
  · intro good
    by_contra! h
    exact (MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one _ _ hlt).not_ge
      ((epsMCA_mono _ h).trans good)
  · intro lt
    by_contra! bad
    exact lt.not_ge (mcaDeltaStar_le_of_bad _ _ bad)

/-- The operational supremum is unchanged at each positive interleaving width. -/
theorem interleaved_threshold {p k B : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 1 ≤ k) (hmax : k ≤ 536870912) (hB : B = p / 2^128) (hpos : 1 ≤ B)
    (hlim : B ≤ upperBudget) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F := ZMod p) (A := Fin width → ZMod p)
      ((code g k) ^⋈ (Fin width)) (epsStar : ℝ≥0∞) = (B : ℝ≥0) / n := by
  have hc := Ownership.evalCode_pred_eq_rsCode hg hk
  unfold code
  rw [hc, mcaDeltaStar_interleaved_eq, ← hc]
  exact threshold hg hk hmax hB hpos hlim

namespace Example

abbrev P : ℕ := 61250826226543930850155988052636038260206862337

set_option maxRecDepth 100000 in
theorem prime_P : P.Prime := by
  apply lucas_primality P 3 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show P-1=2^123*(8521*675977) by decide] at hd
  rcases hq.dvd_mul.mp hd with h|h
  · have x := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst q
    rw [← binaryPow_eq_pow]; decide
  · simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 8521),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 675977)] at h
    rcases h with rfl|rfl <;> rw [← binaryPow_eq_pow] <;> decide

instance : Fact P.Prime := ⟨prime_P⟩

abbrev generator : ZMod P := 830666351068687365643932774045365468737521668

theorem generator_order : orderOf generator = n := by
  apply orderOf_eq_prime_pow (p := 2) (n := 29)
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide

theorem budget : P / 2^128 = 180000000 := by decide

/-- All four prize rates have the same exact 128-bit threshold on one smooth group. -/
theorem four_rates :
    let radius : ℝ≥0 := 180000000 / n
    let star := fun k => mcaDeltaStar (F := ZMod P) (code generator k) (epsStar : ℝ≥0∞)
    star (2^29) = radius ∧ star (2^28) = radius ∧ star (2^27) = radius ∧ star (2^26) = radius :=
  ⟨threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide),
   threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide),
   threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide),
   threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide)⟩

/-- One prime and subgroup give all four exact thresholds at every positive width. -/
theorem four_rates_interleaved (width : ℕ) [NeZero width] :
    let radius : ℝ≥0 := 180000000 / n
    let star := fun k => mcaDeltaStar (F := ZMod P) (A := Fin width → ZMod P)
      ((code generator k) ^⋈ (Fin width)) (epsStar : ℝ≥0∞)
    star (2^29) = radius ∧ star (2^28) = radius ∧ star (2^27) = radius ∧ star (2^26) = radius :=
  ⟨interleaved_threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide) width,
   interleaved_threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide) width,
   interleaved_threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide) width,
   interleaved_threshold generator_order (by decide) (by decide) budget.symm (by decide) (by decide) width⟩

end Example

#print axioms count_upper
#print axioms exact_mass
#print axioms threshold
#print axioms interleaved_good_iff
#print axioms Example.prime_P
#print axioms Example.generator_order
#print axioms Example.four_rates
#print axioms Example.four_rates_interleaved

end ArkLib.ProximityGap.Frontier.FourRatePairBudget
