/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFourPairSmooth
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import CompPoly.Fields.Pasta.Basic
import Mathlib.Tactic.ReduceModChar

/-! # The exact length-256, rate-one-eighth list threshold in the Pasta fields -/

namespace ProximityGap.DyadicList256
open Code GrandChallenges ReflectionListSampling
open scoped NNReal ENNReal

set_option maxRecDepth 4096

/-- The full interval obtained by the cap of three transpositions and the
prescribed-product failure at 33 agreements. -/
def InBand (p : ℕ) : Prop :=
  61229714204650886131205271461942746734 ≤ p/2^128 ∧ p/2^128 ≤ 1544364235623542792536478250736605959624

/-- Every smooth 256-site code of dimension 32 in the field interval first
exceeds the 128-bit prize list budget at 223 errors, for every positive width. -/
theorem threshold {p : ℕ} [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (band : InBand p)
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=256) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ:=Fin m) (ReedSolomon.code D 32 : Set (I → ZMod p))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal)*(Fintype.card (ZMod p) : ENNReal) ↔ δ < (223:ℝ)/256 := by
  have lo : 61229714204650886131205271461942746734*2^128 ≤ p :=
    (Nat.mul_le_mul_right _ band.1).trans (Nat.div_mul_le_self _ _)
  have hpow : 12^(2^8).totient < p^2 :=
    (by decide : 12^(2^8).totient < (61229714204650886131205271461942746734*2^128)^2).trans_le
      (Nat.pow_le_pow_left lo 2)
  rw [ZMod.card,FourRateList128.budget_cast]
  have cert := DyadicFourPairSmooth.threshold (e:=8) (k:=32) (r:=221) (B:=p/2^128) D hn hpow
    (by decide) (by decide) (Or.inr (by simp only [Nat.choose_eq_descFactorial_div_factorial];decide))
    (le_trans (by unfold bound;simp only [Nat.choose_eq_descFactorial_div_factorial];decide) band.1)
    (lt_of_le_of_lt (Nat.mul_le_mul_left _ band.2) (by simp only [Nat.choose_eq_descFactorial_div_factorial];decide)) m hm δ
  simpa only [hn,Nat.reduceAdd,Nat.cast_ofNat] using cert

/-- An explicit 254-bit modulus in the band. -/
abbrev P : ℕ := 443*2^245+1

/-- Full-order Lucas proof with the two factors of P−1. -/
theorem prime : P.Prime := by
  have eq : (3:ZMod P)^(P-1)=1 := by reduce_mod_char
  refine lucas_primality P 3 eq ?_
  intro v hv hd
  rw [show P-1=2^245*443 by decide] at hd
  rcases hv.dvd_mul.mp hd with two|odd
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow two)
    reduce_mod_char
    decide
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 443)).mp odd
    reduce_mod_char
    decide

instance : Fact P.Prime := ⟨prime⟩

/-- The two Pasta base fields and the explicit 254-bit witness satisfy the
complete budget interval. At all three primes ordinary agreement-subset
packing at 34 agreements exceeds the budget. Each admits 256-site cosets. -/
theorem named (p : ℕ) (field : p=Pallas.baseFieldSize ∨ p=Vesta.baseFieldSize ∨ p=P) :
    InBand p ∧ p/2^128 < (256:ℕ).choose 32 / (34:ℕ).choose 32 ∧ 256∣p-1 := by
  rcases field with rfl|rfl|rfl <;> simp only [InBand,Nat.choose_eq_descFactorial_div_factorial] <;> decide

/-- The official rate-one-eighth grand challenge on all domains in the band. -/
theorem grand {p : ℕ} [Fact p.Prime] {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (band : InBand p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=256) (m : ℕ) (hm : 0 < m) :
    grandListDecodingChallengeRs D (prizeDimension (ι:=I) 2) m (prizeThreshold : ℝ≥0) := by
  have hk : prizeDimension (ι:=I) 2=32 := by norm_num [prizeDimension,prizeDenominator,hn]
  rw [hk]
  apply GrandListResolution.to_challenge
  refine ⟨222,by rw [hn];decide,?_,?_⟩
  · apply (threshold band D hn m hm _).mpr
    norm_num [gridPt,hn]
  · apply lt_of_not_ge
    intro h
    have no := (threshold band D hn m hm _).mp h
    norm_num [gridPt,hn] at no

end ProximityGap.DyadicList256
#print axioms ProximityGap.DyadicList256.grand
#print axioms ProximityGap.DyadicList256.prime
#print axioms ProximityGap.DyadicList256.named
