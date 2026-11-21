/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SplitPrimeSixthDensity
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMoment

/-!
# The actual split primes and the ordered sixth-energy condition

The two analytical inputs below have their literal mathematical domains. The
result counts prime fields with the stated bound on the repository's energy.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.ProductionSplitPrimeSixth

open Finset Real SplitPrimeSixthDensity
noncomputable section

abbrev n : ℕ := 2^30
def splitTo (x : ℕ) : Finset ℕ := (range (x+1)).filter fun p => p.Prime ∧ p % n = 1
def window (a b : ℕ) : Finset ℕ := splitTo b \ splitTo a

/-- Ordered equal triple sums on the actual subgroup of the indicated prime field. -/
def energy (p : ℕ) : ℕ :=
  if h : p.Prime then
    let _ : Fact p.Prime := ⟨h⟩
    SubgroupGaussSumSixthMoment.addEnergy3 (Polynomial.nthRootsFinset n (1:ZMod p))
  else 0

def failing (a b : ℕ) : Finset ℕ := (window a b).filter fun p => 15*n^3 < energy p
def passing (a b : ℕ) : Finset ℕ := (window a b).filter fun p => energy p ≤ 15*n^3

/-- The cyclotomic determinant inequality in weighted counting form. -/
def NormBound : Prop := ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % n = 1) →
  ∑ p ∈ S, ((energy p : ℝ) - (15*(n:ℝ)^3-45*(n:ℝ)^2+40*n)) * log p ≤ (n:ℝ)^6/2*log 6

/-- Lee's Corollary 1.1 on this band, with its negative additive constant discarded. -/
def LeeBound : Prop := ∀ x : ℕ, 2^158 ≤ x → x ≤ 2^159 →
  |weight (splitTo x) - (x:ℝ)/2^29| ≤
    (log x/(8*π)+log (n:ℝ)/(2*π)+5.66833)*sqrt x*log x

private theorem mem_window {a b p : ℕ} (h : p ∈ window a b) :
    a < p ∧ p ≤ b ∧ p.Prime ∧ p % n = 1 := by
  obtain ⟨hi,lo⟩ := mem_sdiff.mp h
  obtain ⟨hb,hp⟩ := mem_filter.mp hi
  have hn : p ∉ range (a+1) := fun ha => lo (mem_filter.mpr ⟨ha,hp⟩)
  simp only [mem_range, not_lt] at hn hb
  exact ⟨by omega, by omega, hp⟩

private theorem pass_eq (a b : ℕ) : window a b \ failing a b = passing a b := by
  ext p
  by_cases h : p ∈ window a b <;> simp [failing,passing,h,not_lt]

private theorem weights {a b : ℕ} (hab : a ≤ b) (ha : 2^158 ≤ a) (hb : b ≤ 2^159)
    (hl : LeeBound) (hn : NormBound) :
    ((b:ℝ)-a)/2^29-2^92 < weight (window a b) ∧ weight (failing a b) < 2^120/50 := by
  have hsub : splitTo a ⊆ splitTo b := by
    intro p h
    obtain ⟨h',hp⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_range.mpr (lt_of_lt_of_le (mem_range.mp h') (by omega)),hp⟩
  have herr (x : ℕ) (l : 2^158 ≤ x) (u : x ≤ 2^159) :
      |weight (splitTo x)-(x:ℝ)/2^29| < 2^91 :=
    lee_endpoint_error (x := (x:ℝ)) (by exact_mod_cast l) (by exact_mod_cast u)
      (by simpa only [n,Nat.cast_pow,Nat.cast_ofNat] using hl x l u)
  have hle := (abs_lt.mp (herr a ha (hab.trans hb))).2
  have hre := (abs_lt.mp (herr b (ha.trans hab) hb)).1
  have w := window_weight hle (show (b:ℝ)/2^29-weight (splitTo b) < 2^91 by linarith)
  have heq : weight (window a b) + weight (splitTo a) = weight (splitTo b) := sum_sdiff hsub
  refine ⟨by linarith, bad_weight ?_⟩
  let S := failing a b
  have hS (p : ℕ) (h : p ∈ S) := mem_window (mem_filter.mp h).1
  calc
    (45*(2^30:ℝ)^2-40*2^30)*weight S =
        ∑ p ∈ S, (45*(2^30:ℝ)^2-40*2^30)*log p := by rw [weight, mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun p h => by
      have he : (15:ℝ)*(n:ℝ)^3 < energy p := by exact_mod_cast (mem_filter.mp h).2
      have hpos : 1 ≤ p := by have := (hS p h).1; omega
      have lg : 0 ≤ log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
      apply mul_le_mul_of_nonneg_right _ lg
      dsimp only [n] at *
      push_cast at he ⊢
      linarith
    _ ≤ (n:ℝ)^6/2*log 6 := hn S fun p h => (hS p h).2.2
    _ = _ := by norm_num [n]

/-- The sixth-moment failure fraction and passing count in the whole production band. -/
theorem full_band (hl : LeeBound) (hn : NormBound) :
    25000*(failing (2^158) (2^159)).card < (window (2^158) (2^159)).card ∧
    2^122 < (passing (2^158) (2^159)).card := by
  have hw := weights (a := 2^158) (b := 2^159) (by norm_num) le_rfl le_rfl hl hn
  have hp (p : ℕ) (h : p ∈ window (2^158) (2^159)) := mem_window h
  have hbhd : ∀ p ∈ window (2^158) (2^159), 2^158 ≤ p ∧ p ≤ 2^159 :=
    fun p h => ⟨(hp p h).1.le,(hp p h).2.1⟩
  have hc : (2:ℝ)^129-2^92 < weight (window (2^158) (2^159)) := by
    convert hw.1 using 1
    norm_num
  rw [← pass_eq]
  exact ⟨band_failure_fraction (Finset.filter_subset ..) hbhd hc hw.2,
    band_passing_count (Finset.filter_subset ..) hbhd hc hw.2⟩

/-- A count in each individual window, with no alignment hypothesis on its left endpoint. -/
theorem short_window (hl : LeeBound) (hn : NormBound) (a : ℕ)
    (lo : 2^158 ≤ a) (hi : a+2^144 ≤ 2^159) :
    2^106 < (passing a (a+2^144)).card := by
  have hw := weights (a := a) (b := a+2^144) (by omega) lo hi hl hn
  have hmass : (2:ℝ)^115-2^92 < weight (window a (a+2^144)) := by
    convert hw.1 using 1
    push_cast
    ring
  rw [← pass_eq]
  apply narrow_passing_count (Finset.filter_subset ..) _ hmass hw.2
  intro p h
  obtain ⟨l,u,_⟩ := mem_window h
  exact ⟨lo.trans l.le,u.trans hi⟩

#print axioms full_band
#print axioms short_window

end
end ArkLib.ProximityGap.Frontier.ProductionSplitPrimeSixth
