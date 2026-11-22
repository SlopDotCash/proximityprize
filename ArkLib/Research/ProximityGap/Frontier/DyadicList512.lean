/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicList256Realizations
import ArkLib.Research.ProximityGap.Frontier.DyadicMeanPairThreshold

/-! # Exact rate-one-eighth list failure at 447 errors on a 512-site smooth domain -/

namespace ProximityGap.DyadicList512
open Code GrandChallenges ReflectionListSampling
open scoped NNReal ENNReal

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

/-- Complete interval obtained by three-transposition sampling at 66 agreements
and the prescribed-product lower bound at 65 agreements. -/
def InBand (p : ℕ) : Prop :=
  4627008003158041656823473239852458024646734572146967108113412016493338518178611 ≤ p/2^128 ∧
  p/2^128 ≤ 430017946753228893985672921850874793509645937925331218258410292473479190614189224

/-- The exact list-budget comparison holds at all widths on every smooth
length-512, dimension-64 domain throughout the interval. -/
theorem threshold {p : ℕ} [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (band : InBand p)
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=512) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ:=Fin m) (ReedSolomon.code D 64 : Set (I → ZMod p))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal)*(Fintype.card (ZMod p) : ENNReal) ↔ δ < (447:ℝ)/512 := by
  let U := 4627008003158041656823473239852458024646734572146967108113412016493338518178611
  have lo : U*2^128≤p := (Nat.mul_le_mul_right _ band.1).trans (Nat.div_mul_le_self _ _)
  have hpow : 54^(2^9).totient < p^4 :=
    (by decide : 54^(2^9).totient<(U*2^128)^4).trans_le (Nat.pow_le_pow_left lo 4)
  rw [ZMod.card,FourRateList128.budget_cast]
  have cert := DyadicMeanPairThreshold.threshold (e:=9) (k:=64) (r:=445) (B:=p/2^128) D hn hpow
    (by decide) (by decide) (Or.inr (by simp only [Nat.choose_eq_descFactorial_div_factorial];decide))
    (le_trans (by unfold bound;simp only [Nat.choose_eq_descFactorial_div_factorial];decide) band.1)
    (lt_of_le_of_lt (Nat.mul_le_mul_left _ band.2) (by simp only [Nat.choose_eq_descFactorial_div_factorial];decide)) m hm δ
  simpa only [hn,Nat.reduceAdd,Nat.cast_ofNat] using cert

/-- A 390-bit split prime in the band. -/
abbrev P : ℕ := 235*2^382+1

/-- Three is a full-order Lucas witness at the factors 2, 5 and 47. -/
theorem prime : P.Prime := by
  have eq : (3:ZMod P)^(P-1)=1 := by reduce_mod_char
  refine lucas_primality P 3 eq ?_
  intro v hv hd
  rw [show P-1=2^382*(5*47) by decide] at hd
  rcases hv.dvd_mul.mp hd with two|odd
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow two)
    reduce_mod_char
    decide
  · rcases hv.dvd_mul.mp odd with five|rest
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 5)).mp five
      reduce_mod_char
      decide
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 47)).mp rest
      reduce_mod_char
      decide

instance : Fact P.Prime := ⟨prime⟩

/-- Both the uniform height-12 test and ordinary agreement-subset packing
miss this prime at 66 agreements. -/
theorem window : InBand P ∧ P^2 ≤ 12^(Nat.totient 512) ∧ P/2^128 < (512:ℕ).choose 64 / (66:ℕ).choose 64 ∧
    512∣P-1 := by
  simp only [InBand,Nat.choose_eq_descFactorial_div_factorial];decide

/-- A genuine length-512 smooth domain realizes the sharp endpoint; the
preceding comparison holds on all its cosets and reorderings by the threshold theorem. -/
theorem realized : ∃ D : Fin 512 ↪ ZMod P, Nonempty (ReedSolomon.Smooth D) ∧ ∀ m : ℕ, 0 < m → ∀ δ : ℝ,
    (Lambda (interleavedCodeSet (κ:=Fin m) (ReedSolomon.code D 64 : Set (Fin 512 → ZMod P))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal)*(Fintype.card (ZMod P):ENNReal) ↔ δ < (447:ℝ)/512 := by
  obtain ⟨D,⟨sm⟩⟩ := DyadicList256.exists_domain (e:=9) window.2.2.2
  exact ⟨D,⟨sm⟩,fun m hm δ => threshold window.1 D (Fintype.card_fin _) m hm δ⟩

/-- The official rate-one-eighth grand challenge on all domains in the band. -/
theorem grand {p : ℕ} [Fact p.Prime] {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (band : InBand p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=512) (m : ℕ) (hm : 0 < m) :
    grandListDecodingChallengeRs D (prizeDimension (ι:=I) 2) m (prizeThreshold : ℝ≥0) := by
  have hk : prizeDimension (ι:=I) 2=64 := by norm_num [prizeDimension,prizeDenominator,hn]
  rw [hk]
  apply GrandListResolution.to_challenge
  refine ⟨446,by rw [hn];decide,?_,?_⟩
  · apply (threshold band D hn m hm _).mpr
    norm_num [gridPt,hn]
  · apply lt_of_not_ge
    intro h
    have no := (threshold band D hn m hm _).mp h
    norm_num [gridPt,hn] at no

end ProximityGap.DyadicList512
#print axioms ProximityGap.DyadicList512.realized
#print axioms ProximityGap.DyadicList512.grand
