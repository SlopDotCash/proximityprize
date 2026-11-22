/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReflectionListArithmetic
import ArkLib.Research.ProximityGap.Frontier.ReflectionListTranspositions
import ArkLib.Research.ProximityGap.Frontier.DenseMobiusTranspositions
import ArkLib.Research.ProximityGap.Frontier.Smooth128Involutions
import ArkLib.Research.ProximityGap.Frontier.SmoothDeepMcaThreshold

/-! # Exact list thresholds in the interval supplied by pair sampling -/
namespace ProximityGap.ReflectionListSampling

open Finset Code

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F]

/-- Natural list upper bound for k+2 agreements when sampling r=n-k-3 sites. -/
def bound (k r T : ℕ) := max 1 ((k+3+r).choose r*T/(((r+1).choose 2-(r+1)/2)*(k+1)))

omit [DecidableEq I] in
/-- The smooth common-product construction exceeds the budget at the successor
error count, independently of the sampling upper bound at its predecessor. -/
theorem strict_radius_of_product [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D]
    {k r B : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r)
    (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (good : Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (B : ℕ∞)) : δ<((r+2 : ℕ):ℝ)/(Fintype.card I : ℝ) := by
  have hk' : 0<k := Nat.pos_of_ne_zero (NeZero.ne k)
  by_contra! bad
  have scalar := SmoothDeepMcaThreshold.smooth_list_lower D (k:=k) (a:=0) (L:=B) hk'
    (by simpa only [hn,pow_zero,Nat.mul_one,Nat.add_zero] using lower)
  have eq : Fintype.card I-(k+1+0)=r+2 := by omega
  rw [eq] at scalar
  let diag : F → Fin m → F := fun x _ => x
  have inj : Function.Injective diag := fun _ _ he => congrFun he ⟨0,hm⟩
  have lift' := Lambda_le_of_injective_comp (e:=diag) inj
    (C:=(ReedSolomon.code D k : Set (I → F)))
    (D:=interleavedCodeSet (κ:=Fin m) (ReedSolomon.code D k : Set (I → F)))
    (fun _ h _ => h) δ
  exact (not_lt_of_ge good) (scalar.trans_le ((Lambda_mono bad).trans lift'))

/-- The complete threshold at every positive width in the budget interval where
nonreflection sampling at k+2 agreements and the product lower bound at k+1
agreements straddle the budget. -/
theorem threshold_of_payment [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D]
    {k r T B : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r) (hr : 2≤r)
    (payment : RowBudget k r (((r+1).choose 2-(r+1)/2)*(k+1)))
    (rigid : PairCap D T) (hT : 1≤T) (upper : bound k r T≤B)
    (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (B : ℕ∞) ↔ δ<((r+2 : ℕ):ℝ)/(Fintype.card I : ℝ) := by
  have npos : (0:ℝ)<Fintype.card I := by exact_mod_cast (hn ▸ (by omega : 0<k+3+r))
  constructor
  · exact strict_radius_of_product D hn lower m hm δ
  · intro safe
    have c : (r+1).choose 2 ≥ r := by
      rw [Nat.choose_succ_succ' r 1,Nat.choose_one_right];omega
    have L : 0<((r+1).choose 2-(r+1)/2)*(k+1) := Nat.mul_pos (by omega) (by omega)
    apply (interleaved D hn rigid hT L payment m δ
      (by simpa only [Nat.cast_add,Nat.cast_ofNat] using (lt_div_iff₀ npos).mp safe)).trans
    exact_mod_cast upper

/-- At half rate or higher the integer payment is automatic. -/
theorem threshold [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D]
    {k r T B : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r) (hr : 2≤r) (hk : r≤k)
    (rigid : PairCap D T) (hT : 1≤T) (upper : bound k r T≤B)
    (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (B : ℕ∞) ↔ δ<((r+2 : ℕ):ℝ)/(Fintype.card I : ℝ) :=
  threshold_of_payment D hn hr (endpoint_payment hk) rigid hT upper lower m hm δ

/-- The Euler argument bounds the nonreflection pair fibers on every proper
smooth coset in a prime field. -/
theorem prime_pairCap {p n : ℕ} [Fact p.Prime] (D : I ↪ ZMod p) [ReedSolomon.Smooth D]
    (hn : Fintype.card I=n) (proper : n<p-1) (hn2 : 2≤n) : PairCap D ((n+1)/3) := by
  classical
  obtain ⟨f,hf⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let : Fintype H := Fintype.ofEquiv I f
  have ch : Fintype.card H=n := (Fintype.card_congr f).symm.trans hn
  have divides : n∣p-1 := by
    simpa only [Nat.card_eq_fintype_card,ch,ZMod.card_units] using H.card_subgroup_dvd_card
  let s := ReedSolomon.Smooth.a D
  have powers (i : I) : (D i)^n=(s : ZMod p)^n := by
    rw [hf,mul_pow]
    have unit : (f i)^n=1 := ch ▸ pow_card_eq_one
    have toF := congrArg (fun g : H => ((g:(ZMod p)ˣ):ZMod p)) unit
    change (((f i):(ZMod p)ˣ):ZMod p)^n=1 at toF
    rw [toF,mul_one]
  have nz (i : I) : D i ≠ 0 := hf i ▸ mul_ne_zero s.ne_zero (f i).val.ne_zero
  exact pairCap_of_involutions D (by omega) nz
    (DenseMobiusTranspositions.prime_coset D hn (pow_ne_zero n s.ne_zero) powers
      (by omega) proper divides)

/-- T=3 for every smooth 128-site domain over all sponsor-size prime fields. -/
theorem prime_pairCap128 {p : ℕ} [Fact p.Prime] (hp : 2^128≤p) (D : I ↪ ZMod p)
    [ReedSolomon.Smooth D] (hn : Fintype.card I=128) : PairCap D 3 := by
  obtain ⟨e,he⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  have nz (i) : D i≠0 := he i ▸ mul_ne_zero (ReedSolomon.Smooth.a D).ne_zero (e i).val.ne_zero
  exact pairCap_of_involutions D (by decide) nz (Smooth128Involutions.dihedral hp D hn)

/-- For a proper smooth prime-field coset the Euler cap and endpoint payment
give an exact threshold from integer budget inequalities at all sponsor rates
with k≥6144, independently of the interleaving width. -/
theorem prime_threshold {p : ℕ} [Fact p.Prime] (D : I ↪ ZMod p) [ReedSolomon.Smooth D]
    {k r B : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r) (hr : 2≤r)
    (large : 6144≤k) (rate : r+1≤16*k) (proper : k+3+r<p-1)
    (upper : bound k r ((k+3+r+1)/3) ≤ B)
    (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → ZMod p))) δ ≤
      (B : ℕ∞) ↔ δ<((r+2 : ℕ):ℝ)/(Fintype.card I : ℝ) :=
  threshold_of_payment D hn hr (sponsor_payment large rate)
    (prime_pairCap D hn proper (by omega)) (by omega) upper lower m hm δ

end ProximityGap.ReflectionListSampling

#print axioms ProximityGap.ReflectionListSampling.threshold
#print axioms ProximityGap.ReflectionListSampling.prime_pairCap
#print axioms ProximityGap.ReflectionListSampling.prime_pairCap128

#print axioms ProximityGap.ReflectionListSampling.prime_threshold
