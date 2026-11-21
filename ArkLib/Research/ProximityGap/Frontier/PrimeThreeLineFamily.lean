/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeManyLinePhase

/-! # An unbounded prime-field family at 128-bit security

For each prime p use length floor(p/2^129)+1 and dimension floor(n/2^125).
All evaluation embeddings have the same eventual first failing index along
every sequence of primes tending to infinity. The limiting field-size slope
times the rate is 16, above the prime three-head separation cost 13.
-/
set_option autoImplicit false
namespace ProximityGap.PrimeThreeLineFamily
open Filter Topology MCAThresholdLedger
open scoped NNReal ENNReal

/-- The length chosen for the 128-bit example. -/
abbrev length (p : ℕ) := p/2^129+1

/-- Any sequence of primes tending to infinity realizes the exact three-head
crossing on all domains, with no arithmetic progression condition on the primes. -/
theorem exact_threshold (p : ℕ → ℕ) [∀ i, Fact (p i).Prime] (hp : Tendsto p atTop atTop)
    (x : ∀ i, Fin (length (p i)) ↪ ZMod (p i)) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (length (p i)/2^125) : Set (Fin (length (p i)) → ZMod (p i)))
      (1/(2:ℝ≥0∞)^128) = ((p i/2^128/3:ℕ):ℝ≥0)/length (p i) := by
  let n i := length (p i)
  have hn : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hp.eventually (eventually_ge_atTop (b*2^129))] with i hi
    exact (Nat.le_div_iff_mul_le (by decide : 0<2^129)).mpr hi |>.trans (Nat.le_succ _)
  have diag (f : ℕ → ℕ) [∀ i, NeZero (f i)] :
      Tendsto (fun i => (f i:ℝ)/f i) atTop (𝓝 (1:ℝ)) := by
    apply tendsto_const_nhds.congr
    exact fun i => (div_self (by exact_mod_cast NeZero.ne (f i))).symm
  have size := LinearFieldBudgetLimit.floor_limit p p (2^129) (by decide) hp (diag p)
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hp
  have reciprocal : Tendsto (fun i => (n i:ℝ)/p i) atTop (𝓝 (1/(2:ℝ)^129)) := by
    have sum := size.add tiny
    rw [add_zero,Nat.cast_pow,Nat.cast_ofNat] at sum
    apply sum.congr
    intro i
    change ((p i/2^129:ℕ):ℝ)/p i+1/p i=(((p i/2^129)+1:ℕ):ℝ)/p i
    rw [Nat.cast_add,Nat.cast_one,add_div]
  have slope : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 ((2:ℝ)^129)) := by
    simpa only [inv_div,div_one] using reciprocal.inv₀ (by positivity)
  have rate := LinearFieldBudgetLimit.floor_limit n n (2^125) (by decide) hn (diag n)
  have result := PrimeManyLinePhase.exact_threshold p n (fun i => n i/2^125) x 3 (2^128)
    (by decide) (by decide) hn slope rate (by positivity) (a:=(2:ℝ)/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa only [n,Nat.cast_pow,Nat.cast_ofNat] using result

/-- The eventual threshold is uniform over every sufficiently large prime
and every injective domain of the prescribed length. -/
theorem all_large_primes : ∃ P : ℕ, ∀ (p : ℕ), P≤p → ∀ [Fact p.Prime]
    (x : Fin (length p) ↪ ZMod p),
    mcaDeltaStar (F:=ZMod p) (ReedSolomon.code x (length p/2^125) :
      Set (Fin (length p) → ZMod p)) (1/(2:ℝ≥0∞)^128) =
      ((p/2^128/3:ℕ):ℝ≥0)/length p := by
  classical
  by_contra! fail
  choose p large prime x bad using fail
  let : ∀ i, Fact (p i).Prime := prime
  have grows : Tendsto p atTop atTop := tendsto_atTop.mpr fun a =>
    (eventually_ge_atTop a).mono fun i hi => hi.trans (large i)
  obtain ⟨i,hi⟩ := (exact_threshold p grows x).exists
  exact bad i hi

/-- Every prime actually admits an embedding of the length in the example. -/
noncomputable def domain (p : ℕ) [Fact p.Prime] : Fin (length p) ↪ ZMod p :=
  (Fin.castLEEmb (show length p ≤ Fintype.card (ZMod p) by
    rw [ZMod.card]
    exact Nat.div_lt_self (Fact.out (p:=p.Prime)).pos (by decide))).trans
    (Fintype.equivFin (ZMod p)).symm.toEmbedding

end ProximityGap.PrimeThreeLineFamily
#print axioms ProximityGap.PrimeThreeLineFamily.exact_threshold
#print axioms ProximityGap.PrimeThreeLineFamily.all_large_primes
