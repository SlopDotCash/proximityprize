/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA

/-! # The half-rate unique-decoding endpoint on arbitrary domains

At exactly h errors for a length-4h, dimension-2h code, every received
pair has at most 3(h+1) genuinely bad scalars. Both nominated production
fields consequently remain sound at one quarter.
-/

set_option autoImplicit false
open Finset Code ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ApolarHalfBreakpoint

/-- Exactly at the half-rate Hamming breakpoint, any evaluation domain and
received pair have at most 3(h+1) bad scalar parameters. -/
theorem family_card {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {dom : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    {h : ℕ} (fam : BadScalarRichPointFamily dom (2*h) δ u) (hh : 0<h)
    (hn : Fintype.card ι=4*h) (ht : 3*h ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊) :
    fam.G.card ≤ 3*(h+1) := by
  have hs := SharpApolarMCA.family_bound (e:=h) (d:=2*h-1) fam fam.G Finset.Subset.rfl
    (by omega) (by omega) (by omega) (by omega) (by
      rw [show Fintype.card ι-h = 3*h by omega]
      exact ht) (by omega)
  rwa [show 2*h-1+2-2*h=1 by omega,Nat.div_one,max_eq_right (by omega)] at hs

private abbrev n : ℕ := 1073741824
private abbrev h : ℕ := 268435456

/-- On any length-2³⁰ smooth prime-field domain the scalar numerator at one
quarter is at most 805306371. -/
theorem mass {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g=n) :
    epsMCA (F := ZMod p) (RateHalfApolarThreshold.code g) (1/4) ≤
      ((805306371:ℕ):ℝ≥0∞)/(p:ℝ≥0∞) := by
  classical
  let dom := KKH26RegimeSplit.powDomain g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
  have hc : RateHalfApolarThreshold.code g = (ReedSolomon.code dom (2*h) : Set (Fin n → ZMod p)) :=
    KKH26RegimeSplit.evalCode_eq_reedSolomon g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg) 536870911
  rw [hc]
  apply (epsMCA_le_of_badCount_le _ _ 805306371 ?_).trans (by rw [ZMod.card])
  intro u
  let fam := canonicalBadScalarRichPointFamily dom (1/4) u (by decide : 1≤2*h)
  apply family_card fam (by decide) (Fintype.card_fin _)
  have heq : (1/4:ℝ≥0)=(h:ℝ≥0)/n := by norm_num [n,h]
  rw [heq,TwoCorePackingThreshold.agreement_ceiling h (by decide)]
  decide

/-- When the budget admits 805306371 bad scalars, the operational endpoint
is at least one full Hamming step above one quarter. -/
theorem operational_floor {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g=n)
    (hb : 805306371 ≤ p/2^128) :
    (268435457:ℝ≥0)/1073741824 ≤ mcaDeltaStar (F := ZMod p)
      (RateHalfApolarThreshold.code g) (epsStar:ℝ≥0∞) := by
  have good := (mass hg).trans (natCast_div_le_inv_of_mul_le (Q:=2^128) (by decide)
    (Fact.out (p:=p.Prime)).pos ((Nat.mul_le_mul_right _ hb).trans (Nat.div_mul_le_self ..)))
  rw [← epsStar_coe_eq_natCast_inv] at good
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a:=268435457) (by decide)
    (by decide : 268435457≤n)
  change epsMCA (F := ZMod p) (RateHalfApolarThreshold.code g) (((268435456:ℕ):ℝ≥0)/n) ≤ _
  rwa [show ((268435456:ℕ):ℝ≥0)/n=1/4 by norm_num [n]]

local instance : Fact (Nat.Prime PrizeShapePrimeP30.P) := ⟨PrizeShapePrimeP30.prime_P⟩
local instance : Fact (Nat.Prime PrizeShapePrimeP30Second.P) := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- Both originally nominated smooth prime fields admit the one-step
operational floor at rate one half. -/
theorem named_prime_floors :
    (268435457:ℝ≥0)/1073741824 ≤ mcaDeltaStar (F := ZMod PrizeShapePrimeP30.P)
      (RateHalfApolarThreshold.code PrizeShapePrimeP30.g) (epsStar:ℝ≥0∞) ∧
    (268435457:ℝ≥0)/1073741824 ≤ mcaDeltaStar (F := ZMod PrizeShapePrimeP30Second.P)
      (RateHalfApolarThreshold.code PrizeShapePrimeP30Second.g) (epsStar:ℝ≥0∞) :=
  ⟨operational_floor PrizeShapePrimeP30.orderOf_g (by rw [PrizeShapePrimeP30.P_div_two_pow_128];decide),
    operational_floor PrizeShapePrimeP30Second.orderOf_g (by rw [PrizeShapePrimeP30Second.P_div_two_pow_128];decide)⟩

#print axioms family_card
#print axioms mass
#print axioms operational_floor
#print axioms named_prime_floors

end ArkLib.ProximityGap.Frontier.ApolarHalfBreakpoint
