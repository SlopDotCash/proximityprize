/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.WeightedTwoErrorList
import ArkLib.Research.ProximityGap.Frontier.Smooth128PrimeBand
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary

/-! # The 64-site half-rate threshold from an embedded two-error certificate -/

namespace ProximityGap.WeightedList64

open Finset Code TwoErrorSlice TwoErrorSliceThreshold
open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)

set_option exponentiation.threshold 1000
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

private theorem power_add {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 64) (a b : Fin 64) :
    z^((a+b : Fin 64):ℕ)=z^a.val*z^b.val := by
  rw [Fin.val_add,←pow_add]
  simpa only [← hz.eq_orderOf] using pow_mod_orderOf z (a.val+b.val)

private theorem antipodal {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 64) : z^32= -1 := by
  have square : (z^32)^2=1 := by rw [←pow_mul]; exact hz.pow_eq_one
  exact (sq_eq_one_iff.mp square).resolve_left (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))

private theorem site_ratio {I J F : Type*} [Field F] (D : J ↪ F) (j : I → J)
    (idx : I → Fin 64) {z c : F} (hz : IsPrimitiveRoot z 64) (hc : c≠0)
    (sites : ∀ i,D (j i)=c*z^(idx i).val) (u v i : I) :
    ratio D (j u) (j v) (j i)=(z^(idx i-idx u).val-1)/(z^(idx i-idx u).val-z^(idx v-idx u).val) := by
  have shift (x) : z^(idx x).val=z^(idx u).val*z^(idx x-idx u).val := by
    rw [←power_add hz,add_comm,sub_add_cancel]
  have nz : z≠0 := by intro h; simpa [h] using hz.pow_eq_one
  rw [ratio,sites,sites,sites,←mul_sub,←mul_sub,mul_div_mul_left _ _ hc,shift v,shift i]
  generalize z^(idx i-idx u).val=x
  generalize z^(idx v-idx u).val=y
  let a := z^(idx u).val
  change (a-a*x)/(a*y-a*x)=(x-1)/(x-y)
  rw [show a-a*x=a*(1-x) by ring,show a*y-a*x=a*(y-x) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ nz),←neg_sub x 1,←neg_sub x y,neg_div_neg_eq]

private theorem den {I F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 64) (f : I ↪ Fin 64)
    (u v i : I) (ne : i≠v) : z^(f i-f u).val ≠ z^(f v-f u).val := by
  intro h
  have same : f i-f u=f v-f u := Fin.ext (hz.pow_inj (f i-f u).isLt (f v-f u).isLt h)
  exact ne (f.injective (sub_left_inj.mp same))

private theorem coordinates {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=64) :
    ∃ (z c : ZMod p) (idx : I ↪ Fin 64), IsPrimitiveRoot z 64 ∧ c≠0 ∧ ∀ i,D i=c*z^(idx i).val := by
  classical
  let H := ReedSolomon.Smooth.H D
  obtain ⟨h,he⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let : Fintype H := Fintype.ofEquiv I h
  have card : Fintype.card H=64 := (Fintype.card_congr h).symm.trans hn
  obtain ⟨a,ha⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := H)).mp inferInstance
  let z := ((a : (ZMod p)ˣ) : ZMod p)
  have prim : IsPrimitiveRoot z 64 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    change orderOf ((a : (ZMod p)ˣ) : ZMod p)=64
    rw [orderOf_units,Subgroup.orderOf_coe,ha,Nat.card_eq_fintype_card,card]
  let orbit (i : Fin 64) : H := a^i.val
  have inj : Function.Injective orbit := fun i j eq => Fin.ext
    (prim.pow_inj i.isLt j.isLt (congrArg (fun b : H => ((b:(ZMod p)ˣ):ZMod p)) eq))
  let f := Equiv.ofBijective orbit ((Fintype.bijective_iff_injective_and_card orbit).mpr
    ⟨inj,(Fintype.card_fin _).trans card.symm⟩)
  refine ⟨z,ReedSolomon.Smooth.a D,(h.trans f.symm).toEmbedding,prim,(ReedSolomon.Smooth.a D).ne_zero,?_⟩
  intro i
  rw [he i]
  apply congrArg ((ReedSolomon.Smooth.a D : ZMod p) * ·)
  exact (congrArg (fun b : H => ((b:(ZMod p)ˣ):ZMod p)) (f.apply_symm_apply (h i))).symm

/-- Transfer a 64-site source orbit directly into the even sites of the
237-bit reference 128-orbit. The norm test uses the source order 64. -/
theorem penalty_cap {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (hp : 2^112<p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=64) :
    PenaltyCap D 12 := by
  classical
  let : NeZero (64:ZMod p) := ⟨fun h => hp.not_ge (by
    have := Nat.le_of_dvd (by decide : 0<64) ((ZMod.natCast_eq_zero_iff 64 p).mp h); omega)⟩
  let : NeZero (64:ZMod P) := ⟨by decide⟩
  let : NeZero (128:ZMod P) := ⟨by decide⟩
  let : NeZero (128:AuxiliaryRatioSlotFacts.F) := ⟨by decide⟩
  have target := penaltyBound_of_six domain237 AuxiliaryRatioSlotFacts.domain root237
    (AuxiliaryRatioSlotData.root : AuxiliaryRatioSlotFacts.F) primitive237 AuxiliaryRatioSlotFacts.primitive
    (fun _ => rfl) (fun _ => rfl) (by decide) AuxiliarySixRows.six
  let w := root237^2
  have hw : IsPrimitiveRoot w 64 := primitive237.pow_of_dvd (show 2≠0 by decide) (by decide)
  obtain ⟨z,c,idx,hz,hc,sites⟩ := coordinates D hn
  let e : I ↪ Fin 128 := idx.trans ⟨fun i => ⟨2*i.val,by omega⟩,fun i j h => Fin.ext (by
    have eq := congrArg Fin.val h
    change 2*i.val=2*j.val at eq
    omega)⟩
  have eval (i) : domain237 (e i)=w^(idx i).val := by
    change root237^(2*(idx i).val)=(root237^2)^(idx i).val
    rw [pow_mul]
  apply penaltyBound_transfer D domain237 e _ _ target
  · intro u v ne anti h
    have pow : w^(idx u).val=w^((idx v+32 : Fin 64).val) := by
      rw [power_add hw,show ((32:Fin 64):ℕ)=32 by decide,antipodal hw,mul_neg_one]
      simpa only [eval] using h
    have equ : idx u=idx v+32 := Fin.ext (hw.pow_inj (idx u).isLt (idx v+32).isLt pow)
    apply anti
    rw [sites,sites,equ,power_add hz,show ((32:Fin 64):ℕ)=32 by decide,antipodal hz,mul_neg_one,mul_neg]
  · intro u v ne anti
    apply preserves_at_from_coordinates D domain237 e u v hz hw (by decide)
      (fun i => (idx i-idx u).val) (idx v-idx u).val
      (site_ratio D id idx hz hc sites u v)
      (site_ratio domain237 e idx hw one_ne_zero (by simpa only [one_mul] using eval) u v)
      (den hz idx u v) (den hw idx u v)
    rw [show Nat.totient 64=32 by decide,show 2^(7*32)=(2^112)^2 by decide]
    exact Nat.pow_lt_pow_left hp (by decide)

open GrandChallenges ReflectionListSampling
open scoped NNReal ENNReal

/-- The interval where the half-rate threshold has 31 errors as its first
failure. The smaller dimensions are classified by their interpolation boundaries. -/
def InBand (p : ℕ) : Prop :=
  220447348371475 ≤ p/2^128 ∧ p/2^128 ≤ 27767032438524098

/-- First over-budget errors in decreasing rate order at length 64. -/
def firstBad (B : ℕ) : Fin 4 → ℕ := ![31,if 488526937079580≤B then 49 else 48,57,61]

/-- Exact four-rate list thresholds on every smooth length-64 prime-field
domain in the indicated budget interval. -/
theorem thresholds {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (band : InBand p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=64)
    (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι:=I) j) m) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card (ZMod p) ↔ δ<(firstBad (p/2^128) j : ℝ)/64 := by
  let B := p/2^128
  have pos : 2^112<p := by
    have lower := (Nat.mul_le_mul_right (2^128) band.1).trans (Nat.div_mul_le_self p (2^128))
    exact (by decide : 2^112<220447348371475*2^128).trans_le lower
  have half :
      (Lambda (ListInterpolationBoundary.words D 32 m) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card (ZMod p) ↔ δ<31/64 := by
    rw [FourRateList128.budget_cast,ZMod.card]
    have hu : weighted_bound 32 29 12 ≤ B := by
      apply le_trans _ band.1
      unfold weighted_bound
      simp only [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have hl : (32+3+29)*B < (32+3+29).choose (32+1) := by
      apply (Nat.mul_le_mul_left _ band.2).trans_lt
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have h := weighted_threshold D (k:=32) (r:=29) (S:=12) hn (by decide) (by decide)
      (endpoint_payment (by decide)) (penalty_cap pos D hn) hu hl m hm δ
    simpa only [hn,Nat.reduceAdd,Nat.cast_ofNat] using h
  have low (k : ℕ) (hk : k=16 ∨ k=8 ∨ k=4) :=
    ListInterpolationBoundary.prize_good_iff D (k:=k) (m:=m) (by omega) (by rw [hn];omega) hm (by
      rw [hn,ZMod.card]
      apply le_trans _ band.1
      rcases hk with rfl|rfl|rfl <;> rw [Nat.choose_eq_descFactorial_div_factorial] <;> decide) δ
  have c16 : Nat.choose 64 16=488526937079580 := by rw [Nat.choose_eq_descFactorial_div_factorial];decide
  have c8 : Nat.choose 64 8≤p/2^128 :=
    (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide : Nat.choose 64 8≤220447348371475).trans band.1
  have c4 : Nat.choose 64 4≤p/2^128 :=
    (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide : Nat.choose 64 4≤220447348371475).trans band.1
  fin_cases j
  · simpa [prizeDimension,prizeDenominator,hn,firstBad] using half
  · have h := low 16 (Or.inl rfl)
    rw [hn,ZMod.card,c16] at h
    simpa [prizeDimension,prizeDenominator,hn,firstBad] using h
  · have h := low 8 (Or.inr (.inl rfl))
    rw [hn,ZMod.card,ite_eq_left c8] at h
    simpa [prizeDimension,prizeDenominator,hn,firstBad] using h
  · have h := low 4 (Or.inr (.inr rfl))
    rw [hn,ZMod.card,ite_eq_left c4] at h
    simpa [prizeDimension,prizeDenominator,hn,firstBad] using h

/-- The sponsor's list-decoding predicate throughout the 64-site band. -/
theorem prize {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (band : InBand p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=64)
    (m : ℕ) (hm : 0 < m) : listDecodingPrize D m := by
  refine ⟨hm,PrizeDomainAdmissible.of_smooth D (by rw [hn]; decide),?_⟩
  intro j
  have endpoint := thresholds band D hn j m hm
  apply GrandListResolution.to_challenge
  refine ⟨firstBad (p/2^128) j-1,?_,?_,?_⟩
  all_goals
    have values (b : ℕ) (i : Fin 4) : firstBad b i=31 ∨ firstBad b i=48 ∨
        firstBad b i=49 ∨ firstBad b i=57 ∨ firstBad b i=61 := by
      by_cases h : 488526937079580≤b <;> fin_cases i <;> simp [firstBad,h]
    specialize values (p/2^128) j
  · rw [hn]
    rcases values with h|h|h|h|h <;> rw [h] <;> decide
  · apply (endpoint _).mpr
    rcases values with h|h|h|h|h <;> rw [h] <;> norm_num [gridPt,hn]
  · apply lt_of_not_ge
    intro h
    have bad := (endpoint _).mp h
    rcases values with he|he|he|he|he <;> rw [he] at bad <;> norm_num [gridPt,hn] at bad

/-- A 176-bit prime in the part of the interval first covered by the weighted count. -/
abbrev p176 : ℕ := 441*2^167+1

theorem prime176 : p176.Prime := by
  apply lucas_primality p176 11 (by rw [←ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow];decide)
  intro q hq divides
  rw [show p176-1=3^2*(7^2*2^167) by decide] at divides
  rcases hq.dvd_mul.mp divides with h|h
  · have eq := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp (hq.dvd_of_dvd_pow h)
    subst q
    rw [←ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow];decide
  · rcases hq.dvd_mul.mp h with h|h
    · have eq := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp (hq.dvd_of_dvd_pow h)
      subst q
      rw [←ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow];decide
    · have eq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
      subst q
      rw [←ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow];decide

instance : Fact p176.Prime := ⟨prime176⟩

/-- The concrete prime has an evaluation subgroup of order 64 and a budget
strictly between the weighted and transposition-only sufficient budgets. -/
theorem parameters176 :
    IsPrimitiveRoot (33729119466791983438383980300253466275768829011745313 : ZMod p176) 64 ∧
    InBand p176 ∧ p176/2^128=242442313924608 ∧
    p176/2^128 < ReflectionListSampling.bound 32 29 3 := by
  refine ⟨IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime_pow (p:=2) (n:=5) (by decide) (by decide)),
    by unfold InBand; decide,by decide,?_⟩
  unfold ReflectionListSampling.bound
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- At this prime the four first failing counts are 31, 48, 57 and 61. -/
theorem thresholds176 {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (D : I ↪ ZMod p176) [ReedSolomon.Smooth D] (hn : Fintype.card I=64) (j : Fin 4)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι:=I) j) m) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card (ZMod p176) ↔
      δ<((![31,48,57,61] j : ℕ):ℝ)/64 := by
  have h := thresholds parameters176.2.1 D hn j m hm δ
  have values : firstBad (p176/2^128)=![31,48,57,61] := by rfl
  rwa [values] at h

/-- The actual 64th roots in the displayed prime field realize the sponsor predicate
at every positive interleaving width. -/
theorem realized176 :
    letI : Fintype (rootsOfUnity 64 (ZMod p176)) := Fintype.ofFinite _
    let D := FourRateList128.domain (rootsOfUnity 64 (ZMod p176))
    ∃ sm : ReedSolomon.Smooth D,
      letI := sm
      ∀ m : ℕ, 0 < m → listDecodingPrize D m := by
  classical
  let H := rootsOfUnity 64 (ZMod p176)
  let _ : Fintype H := Fintype.ofFinite _
  have hc : Fintype.card H=64 := Nat.card_eq_fintype_card.symm.trans parameters176.1.card_rootsOfUnity
  let _ := FourRateList128.smooth_of_two_pow H (e:=6) hc
  exact ⟨inferInstance,fun m hm => prize parameters176.2.1 (FourRateList128.domain H) hc m hm⟩

end ProximityGap.WeightedList64

#print axioms ProximityGap.WeightedList64.penalty_cap
#print axioms ProximityGap.WeightedList64.prize

#print axioms ProximityGap.WeightedList64.thresholds176
#print axioms ProximityGap.WeightedList64.realized176
