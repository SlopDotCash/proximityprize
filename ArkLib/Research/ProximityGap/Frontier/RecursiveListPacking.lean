/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Integer packing bounds for supplied Reed–Solomon domains

Successive point incidences give the Johnson–Schönheim packing bound on agreement
sets. Applying the same calculation to their complements improves the bound at
high agreement, including the first step beyond dimension-many agreements.
-/

namespace ProximityGap.RecursiveListPacking

open Finset Code

/-- Upper bound for a family of sets of size at least `t` in an `n`-point
universe with distinct intersections of size less than `k`. -/
def bound (n t : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => n * bound (n - 1) (t - 1) k / t

private theorem family_bound {ι β : Type*} [DecidableEq ι] (k : ℕ)
    (U : Finset ι) (t : ℕ) (T : Finset β) (S : β → Finset ι) (hkt : k ≤ t)
    (hsub : ∀ w ∈ T, S w ⊆ U) (hs : ∀ w ∈ T, t ≤ (S w).card)
    (hpair : ∀ w ∈ T, ∀ v ∈ T, w ≠ v → (S w ∩ S v).card < k) :
    T.card ≤ bound U.card t k := by
  classical
  induction k generalizing U t T S with
  | zero =>
    apply Finset.card_le_one.mpr
    intro w hw v hv
    by_contra hne
    exact Nat.not_lt_zero _ (hpair w hw v hv hne)
  | succ k ih =>
    let above (i : ι) := T.filter fun w ↦ i ∈ S w
    have hpoint (i : ι) (hi : i ∈ U) : (above i).card ≤ bound (U.card - 1) (t - 1) k := by
      rw [← card_erase_of_mem hi]
      apply ih (U.erase i) (t - 1) (above i) (fun w ↦ (S w).erase i) (by omega)
      · intro w hw
        exact erase_subset_erase _ (hsub w (Finset.mem_filter.mp hw).1)
      · intro w hw
        obtain ⟨hwT, hwi⟩ := Finset.mem_filter.mp hw
        rw [card_erase_of_mem hwi]
        exact Nat.sub_le_sub_right (hs w hwT) 1
      · intro w hw v hv hne
        obtain ⟨hwT, hwi⟩ := Finset.mem_filter.mp hw
        obtain ⟨hvT, hvi⟩ := Finset.mem_filter.mp hv
        have hinter : (S w).erase i ∩ (S v).erase i = (S w ∩ S v).erase i := by
          ext x
          simp only [mem_inter, mem_erase]
          tauto
        rw [hinter, card_erase_of_mem (mem_inter.mpr ⟨hwi,hvi⟩)]
        have h := hpair w hwT v hvT hne
        have hp := Finset.card_pos.mpr ⟨i, mem_inter.mpr ⟨hwi,hvi⟩⟩
        omega
    apply (Nat.le_div_iff_mul_le (by omega : 0 < t)).mpr
    calc
      T.card * t = ∑ _w ∈ T, t := by simp
      _ ≤ ∑ w ∈ T, (S w).card := Finset.sum_le_sum hs
      _ = ∑ i ∈ U, (above i).card := by
        calc
          _ = ∑ w ∈ T, ∑ i ∈ U, if i ∈ S w then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [← Finset.card_filter]
            congr 1
            ext x
            simp only [Finset.mem_filter]
            exact ⟨fun hx ↦ ⟨hsub w hw hx,hx⟩, And.right⟩
          _ = _ := by rw [Finset.sum_comm]; simp only [above, Finset.card_filter]
      _ ≤ ∑ _i ∈ U, bound (U.card - 1) (t - 1) k := Finset.sum_le_sum hpoint
      _ = U.card * bound (U.card - 1) (t - 1) k := by simp

/-- Count fixed-size subsets of the agreements and their complementary error sets.
The two recursions give separate bounds for every received center and every width. -/
theorem list_bound {ι F : Type*} [Fintype ι] [Nonempty ι] [Field F]
    (D : ι ↪ F) (k m t : ℕ) (δ : ℝ) (hkt : k ≤ t) (hshape : 2 * t ≤ Fintype.card ι + k)
    (hδ : δ * (Fintype.card ι : ℝ) < (Fintype.card ι : ℝ) - t + 1) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (ι → F))) δ ≤
      (min (bound (Fintype.card ι) t k)
        (bound (Fintype.card ι) (Fintype.card ι - t) (Fintype.card ι + k - 2 * t)) : ℕ) := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro f T hT
  let n := Fintype.card ι
  let A (w : ι → Fin m → F) := univ.filter fun i ↦ w i = f i
  have halarge (w) (hw : w ∈ T) : t ≤ (A w).card := by
    have hd := (mem_closeCodewordsRel_iff.mp (hT w hw)).2
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [relHammingDist_coe, hammingDist_comm, div_le_iff₀ hn] at hd
    have htotal : (agree w f : ℝ) + (hammingDist w f : ℝ) = Fintype.card ι := by
      exact_mod_cast agree_add_hammingDist
    have hround : t < agree w f + 1 := by
      exact_mod_cast (show (t : ℝ) < (agree w f : ℝ) + 1 by linarith)
    change t ≤ agree w f
    omega
  let S (w : ι → Fin m → F) : Finset ι := if h : t ≤ (A w).card then
    (Finset.exists_subset_card_eq h).choose else ∅
  have hS (w) (hw : w ∈ T) : S w ⊆ A w ∧ (S w).card = t := by
    simpa [S, dite_eq_left (halarge w hw)] using
      (Finset.exists_subset_card_eq (halarge w hw)).choose_spec
  have hinter (w) (hw : w ∈ T) (v) (hv : v ∈ T) (hne : w ≠ v) : (S w ∩ S v).card < k := by
    apply lt_of_le_of_lt _ (ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (mem_closeCodewordsRel_iff.mp (hT w hw)).1
      (mem_closeCodewordsRel_iff.mp (hT v hv)).1 hne)
    apply Finset.card_le_card
    intro i hi
    have hw' := (Finset.mem_filter.mp ((hS w hw).1 (Finset.mem_inter.mp hi).1)).2
    have hv' := (Finset.mem_filter.mp ((hS v hv).1 (Finset.mem_inter.mp hi).2)).2
    exact Finset.mem_filter.mpr ⟨mem_univ _, hw'.trans hv'.symm⟩
  apply Nat.le_min.mpr
  constructor
  · exact family_bound k univ t T S hkt (fun _ _ ↦ subset_univ _)
      (fun w hw ↦ (hS w hw).2.ge) hinter
  · apply family_bound (n + k - 2 * t) univ (n - t) T (fun w ↦ univ \ S w) (by omega)
      (fun _ _ ↦ subset_univ _)
    · intro w hw
      simp [card_sdiff_of_subset (subset_univ _), (hS w hw).2, n]
    · intro w hw v hv hne
      rw [← sdiff_union_distrib, card_sdiff_of_subset (subset_univ _), card_univ]
      have hi := hinter w hw v hv hne
      have hsum := card_union_add_card_inter (S w) (S v)
      rw [(hS w hw).2, (hS v hv).2] at hsum
      have hle := Finset.card_le_univ (S w ∪ S v)
      change Fintype.card ι - _ < Fintype.card ι + k - 2 * t
      omega

open scoped ENNReal NNReal

/-- Wherever the recursive packing budget holds at `k+1` agreements and the
`k`-agreement list exceeds the budget, the first failing count is exactly `n-k`. -/
theorem first_failure {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [Finite F]
    (D : ι ↪ F) (k m B : ℕ) (hk : 0 < k) (hm : 0 < m) (hk2 : k + 2 ≤ Fintype.card ι)
    (hbudget : min (bound (Fintype.card ι) (k + 1) k)
      (bound (Fintype.card ι) (Fintype.card ι - (k + 1)) (Fintype.card ι - (k + 2))) ≤ B)
    (hfailure : B < (Fintype.card ι).choose k) (δ : ℝ) :
    Lambda (ListInterpolationBoundary.words D k m) δ ≤ B ↔
      δ < ((Fintype.card ι - k : ℕ) : ℝ) / Fintype.card ι := by
  classical
  letI := Fintype.ofFinite F
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · contrapose!
    intro hδ
    have hle := (Lambda_mono (C := ListInterpolationBoundary.words D k m) hδ)
    rw [ListInterpolationBoundary.at_dimension_agreement D hk (by omega) hm] at hle
    exact (show (B : ℕ∞) < (Fintype.card ι).choose k by exact_mod_cast hfailure).trans_le hle
  · intro hδ
    have hgrid : δ * (Fintype.card ι : ℝ) < (Fintype.card ι : ℝ) - (k + 1 : ℕ) + 1 := by
      rw [lt_div_iff₀ hn, Nat.cast_sub (by omega : k ≤ Fintype.card ι)] at hδ
      push_cast
      linarith
    have hu := list_bound D k m (k + 1) δ (by omega) (by omega) hgrid
    rw [show Fintype.card ι + k - 2 * (k + 1) = Fintype.card ι - (k + 2) by omega] at hu
    exact hu.trans (by exact_mod_cast hbudget)

section Length128

set_option maxRecDepth 12000
open GrandChallenges

/-- At length 128 the complementary packing recursion certifies the half-rate
list bound immediately before capacity. The right inequality in the second
conjunct records what the unrounded agreement-sample bound would charge. -/
theorem half128_arithmetic :
    bound 128 63 62 = 351980102567944271741142966174134400 ∧
    351980102567944271741142966174134400 < Nat.choose 128 64 / 65 := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The four first failing error counts in the stated common field-budget interval. -/
def firstBad128 : Fin 4 → ℕ := ![64, 97, 113, 121]

/-- Four exact list thresholds on every 128-point injection, with the same
finite field and domain for all rates and every positive interleaving width. -/
theorem four_rates_128 {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [Fintype F]
    (D : ι ↪ F) (hn : Fintype.card ι = 128)
    (hlo : 351980102567944271741142966174134400 ≤ Fintype.card F / 2 ^ 128)
    (hhi : Fintype.card F / 2 ^ 128 < Nat.choose 128 64)
    (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := ι) j) m) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card F ↔ δ < (firstBad128 j : ℝ) / 128 := by
  classical
  let B := Fintype.card F / 2 ^ 128
  have lower (k : ℕ) (hk : 0 < k) (hk32 : k ≤ 32)
      (hsmall : Nat.choose 128 k ≤ 351980102567944271741142966174134400) :
      Lambda (ListInterpolationBoundary.words D k m) δ ≤ (B : ℕ∞) ↔
        δ < ((128 - k + 1 : ℕ) : ℝ) / 128 := by
    have hnk : k ≤ Fintype.card ι := hn ▸ (by omega)
    have hc : Nat.choose 128 k ≤ B := hsmall.trans hlo
    have hc' : (Fintype.card ι).choose k ≤ B := hn ▸ hc
    have hh := ListInterpolationBoundary.good_iff D hk hnk hm
      ((Nat.div_le_self _ _).trans hc') (Nat.div_lt_self (Fintype.card_pos : 0 < Fintype.card F)
        (by decide : 1 < 2 ^ 128)) δ
    rw [ite_eq_left hc'] at hh
    simpa [hn] using hh
  rw [FourRateList128.budget_cast]
  fin_cases j
  · have hcap := first_failure D 64 m B (by decide) hm (by rw [hn]; decide)
      (by rw [hn]; exact (min_le_right _ _).trans (half128_arithmetic.1 ▸ hlo))
      (hn ▸ hhi) δ
    simpa [prizeDimension, prizeDenominator, firstBad128, hn, B] using hcap
  · simpa [prizeDimension, prizeDenominator, firstBad128, hn, B] using
      lower 32 (by decide) (by decide) (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)
  · simpa [prizeDimension, prizeDenominator, firstBad128, hn, B] using
      lower 16 (by decide) (by decide) (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)
  · simpa [prizeDimension, prizeDenominator, firstBad128, hn, B] using
      lower 8 (by decide) (by decide) (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- A 247-bit prime for which the rounded complementary estimate is needed
to reach the interpolation endpoint using these packing bounds. -/
abbrev P : ℕ := 2219 * 2 ^ 235 + 1

theorem prime_P : Nat.Prime P := by
  have hmain : (3 : ZMod P) ^ (P - 1) = 1 := by
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
    decide
  refine lucas_primality P 3 hmain ?_
  intro v hv hd
  rw [show P - 1 = 2 ^ 235 * (7 * 317) by decide] at hd
  rcases hv.dvd_mul.mp hd with htwo | hodd
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow htwo)
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
    decide
  · rcases hv.dvd_mul.mp hodd with h7 | h317
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 7)).mp h7
      rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
      decide
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 317)).mp h317
      rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
      decide

instance : Fact (Nat.Prime P) := ⟨prime_P⟩

theorem smooth_generator :
    IsPrimitiveRoot
      (43796106634529630153437654754491160841415788829486980815705453267980984100 : ZMod P) 128 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow (p := 2) (n := 6)
  all_goals rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide

/-- This prime lies below the old packing budget and satisfies the improved budget. -/
theorem prime_budget :
    351980102567944271741142966174134400 ≤ P / 2 ^ 128 ∧ P / 2 ^ 128 < Nat.choose 128 64 / 65 := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The first failing counts on any one supplied length-128 domain of this prime
field. In particular the order-128 subgroup exists by `smooth_generator`. -/
theorem prime_four_rates {ι : Type} [Fintype ι] [Nonempty ι]
    (D : ι ↪ ZMod P) (hn : Fintype.card ι = 128) (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := ι) j) m) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (P : ENNReal) ↔ δ < (firstBad128 j : ℝ) / 128 := by
  have hh := four_rates_128 D hn (by rw [ZMod.card]; exact prime_budget.1)
    (by rw [ZMod.card]; exact prime_budget.2.trans_le (Nat.div_le_self _ 65)) j m hm δ
  simpa [ZMod.card] using hh

end Length128

#print axioms list_bound
#print axioms first_failure
#print axioms four_rates_128
#print axioms prime_P
#print axioms smooth_generator
#print axioms prime_four_rates

end ProximityGap.RecursiveListPacking
