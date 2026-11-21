/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PowerFiberEndpoint
import ArkLib.Research.ProximityGap.Frontier.ApolarHalfBreakpoint

/-! # Exact endpoint count on an explicit length-2³⁰ evaluation domain -/

set_option autoImplicit false
open Finset Polynomial
open Code ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
namespace ArkLib.ProximityGap.Frontier.PowerFiberProduction

abbrev P : ℕ := 267268857013743962100724606304616304664727519233

set_option maxRecDepth 100000 in
/-- Primality of the field containing the three complete power fibers. -/
theorem prime_P : Nat.Prime P := by
  apply lucas_primality P 3 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show P-1=2^114*(17*(47939*15790321)) by decide] at hd
  rcases hq.dvd_mul.mp hd with htwo | hodd
  · have eq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow htwo)
    subst q
    rw [← binaryPow_eq_pow]; decide
  · simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 47939),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 15790321)] at hodd
    rcases hodd with rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

instance : Fact P.Prime := ⟨prime_P⟩

/-- The field admits length-2³⁰ smooth domains and has the indicated scalar budget. -/
theorem parameters : P/2^128=785432578 ∧ 2^30 ∣ P-1 := by decide

open Classical in
/-- A single pair actually realizes this many bad scalars in the explicit
field at the rate-half unique-decoding endpoint. -/
theorem lower :
    ∃ D : Finset (ZMod P), D.card=2^30 ∧
      ∃ u v : D → ZMod P, 805306371 ≤
        (univ.filter fun t : ZMod P => _root_.ProximityGap.mcaEvent
          (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2^29) : Set (D → ZMod P))
          ((268435456:ℝ≥0)/D.card) u v t).card := by
  have h := PowerFiberEndpoint.prime_attain (2^29) 268435456 3 P (by decide)
    (by decide) (by decide) (by decide) (by decide)
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] at h ⊢
  exact h

private noncomputable abbrev code (D : Finset (ZMod P)) :=
  (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2^29) : Set (D → ZMod P))

/-- On one fixed domain the worst-case endpoint probability is exact, and the
full good-radius predicate and operational supremum follow at 128-bit security. -/
theorem exact_endpoint :
    ∃ D : Finset (ZMod P), D.card=2^30 ∧
      epsMCA (F:=ZMod P) (code D) (1/4) = (805306371:ℝ≥0∞)/(P:ℝ≥0∞) ∧
      (∀ δ : ℝ≥0, epsMCA (F:=ZMod P) (code D) δ ≤ (epsStar:ℝ≥0∞) ↔ δ<1/4) ∧
      mcaDeltaStar (F:=ZMod P) (code D) (epsStar:ℝ≥0∞) = 1/4 := by
  classical
  obtain ⟨D,hD,u,v,hu⟩ := lower
  have hn : Fintype.card D = 1073741824 := by rw [Fintype.card_coe,hD];decide
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  let dom := Function.Embedding.subtype (·∈D)
  have hr : (268435456:ℝ≥0)/D.card=1/4 := by rw [hD];norm_num
  rw [hr] at hu
  have hm : epsMCA (F:=ZMod P) (code D) (1/4) = (805306371:ℝ≥0∞)/(P:ℝ≥0∞) := by
    apply le_antisymm
    · apply (epsMCA_le_of_badCount_le _ _ 805306371 ?_).trans (by simp only [ZMod.card,Nat.cast_ofNat,le_refl])
      intro w
      exact ApolarHalfBreakpoint.family_card (h:=268435456)
        (canonicalBadScalarRichPointFamily dom (1/4) w (by decide)) (by decide) hn
        (by
          rw [hn,Nat.cast_ofNat,show (1-(1/4:ℝ≥0))*1073741824 = (805306368:ℕ) by
            rw [tsub_mul,one_mul,div_mul_eq_mul_div];norm_num; exact tsub_eq_of_eq_add (by norm_num)]
          rw [Nat.ceil_natCast])
    · rw [epsMCA_eq_iSup_badCount_div,ZMod.card]
      apply ENNReal.div_le_div_right
      let w : WordStack (ZMod P) (Fin 2) D := ![u,v]
      apply LE.le.trans _ (le_iSup _ w)
      exact_mod_cast hu
  have hb : (epsStar:ℝ≥0∞) < epsMCA (F:=ZMod P) (code D) (1/4) := by
    rw [hm,epsStar_coe_eq_natCast_inv]
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num [P])) (Or.inl (by norm_num)),
      ← ENNReal.div_eq_inv_mul,
      ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num [P]
  have iff' (δ : ℝ≥0) : epsMCA (F:=ZMod P) (code D) δ ≤ (epsStar:ℝ≥0∞) ↔ δ<1/4 := by
    constructor
    · intro h
      by_contra! he
      exact hb.not_ge ((epsMCA_mono _ he).trans h)
    · intro h
      rw [epsStar_coe_eq_natCast_inv]
      apply (epsMCA_le_of_badCount_le _ _ 268435458 ?_).trans
      · rw [ZMod.card]
        exact natCast_div_le_inv_of_mul_le (Q:=2^128) (by decide) prime_P.pos (by decide)
      · intro w
        apply SharpApolarMCA.rate_half_family (canonicalBadScalarRichPointFamily dom δ w (by decide)) hn
        rw [hn]
        apply (Nat.succ_le_iff).mpr
        apply Nat.lt_ceil.mpr
        have hd : δ ≤ 1 := h.le.trans (by norm_num [div_le_iff₀])
        have hh : (4:ℝ≥0)*δ<1 := by rw [lt_div_iff₀ (by norm_num)] at h; simpa [mul_comm] using h
        have hsub := tsub_add_cancel_of_le hd
        change (805306368:ℝ≥0) < (1-δ)*1073741824
        nlinarith only [hh,hsub]
  refine ⟨D,hD,hm,iff',le_antisymm (mcaDeltaStar_le_of_bad _ _ hb) ?_⟩
  by_contra! small
  obtain ⟨δ,hlo,hhi⟩ := exists_between small
  exact hlo.not_ge (le_mcaDeltaStar_of_good _ _ (hhi.le.trans (by norm_num [div_le_iff₀])) ((iff' δ).2 hhi))

#print axioms exact_endpoint
#print axioms prime_P
#print axioms parameters
#print axioms lower
end ArkLib.ProximityGap.Frontier.PowerFiberProduction
