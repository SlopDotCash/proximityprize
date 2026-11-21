/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.OddRedundancyApolar
import ArkLib.Research.ProximityGap.Frontier.OddRedundancySquareLift
import ArkLib.Research.ProximityGap.Frontier.ThreeRegimePrimeThreshold

/-! # The odd-redundancy threshold on smooth domains

The extra scalar at odd h moves exactly one integer budget one grid step.
Every other budget follows the spike, half-distance plateau and two-head formula.
-/
set_option autoImplicit false
namespace ProximityGap.OddSmoothPrimeThreshold
open MCAThresholdLedger ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The first failing index after accounting for the exceptional odd budget. -/
def index (B h : ℕ) := if B=h ∧ h%2=1 then h-1 else ThreeRegimePrimeThreshold.index B h

/-- At h−1 errors the worst-pair numerator on a smooth even-length domain
depends only on the parity of h. -/
theorem endpoint_mass {n k h : ℕ} [NeZero n] (x : Fin n ↪ F) [ReedSolomon.Smooth x]
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h) (even : n%2=0) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (((h-1:ℕ):ℝ≥0)/n) =
      ((h+h%2:ℕ):ℝ≥0∞)/Fintype.card F := by
  by_cases he : h%2=0
  · simpa only [he,Nat.add_zero] using OddRedundancyApolar.endpoint_even x hk rate length large he
  apply le_antisymm (OddRedundancyApolar.endpoint_upper x hk rate length large)
  have ho : h%2=1 := by omega
  rw [ho]
  exact OddRedundancySquareLift.mass x (Fintype.card_fin _) even hk (by omega) length ho

/-- At the unique odd exceptional budget the first failure is h−1, in every finite field.
This endpoint does not require the large-length interpolation estimates. -/
theorem exceptional {n k h Q : ℕ} [NeZero n] (x : Fin n ↪ F) [ReedSolomon.Smooth x]
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h) (even : n%2=0)
    (odd : h%2=1) (security : 0 < Q) (budget : Fintype.card F/Q=h) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let r := ((h-1:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  exact OddRedundancyApolar.exceptional_of_lower x hk rate length large security budget
    (OddRedundancySquareLift.mass x (Fintype.card_fin _) even hk (by omega) length odd) width

/-- The full spike and plateau classification, including odd exceptional budgets,
at any even smooth length and in every finite field. -/
theorem plateau {n k h B Q : ℕ} [NeZero n] (x : Fin n ↪ F) [ReedSolomon.Smooth x]
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h) (even : n%2=0)
    (security : 0 < Q) (budget : Fintype.card F/Q=B) (range : B ≤ 2*h+1) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let r := ((index B h:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  by_cases ex : B=h ∧ h%2=1
  · rw [index,ite_eq_left ex]
    exact exceptional x hk rate length large even ex.2 security (budget.trans ex.1) width
  · have he : index B h=min B h := by rw [index,ite_eq_right ex]; unfold ThreeRegimePrimeThreshold.index;omega
    rw [he]
    exact OddRedundancyApolar.classification x hk rate length large security budget range (by omega) width

/-- For odd redundancy, all tolerances through the two-head window on every
smooth even-length prime-field domain have the stated sharp cutoff. -/
theorem classification {p n k h B Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    [ReedSolomon.Smooth x] (large : 65536 ≤ n) (hk : 3 ≤ k) (rate : 3*k ≤ n)
    (length : n=k+2*h-1) (even : n%2=0) (two : 2 ≤ Q) (budget : p/Q=B)
    (ceiling : B/2+DoubleQuadraticThreshold.agreements n k ≤ n+1) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let r := ((index B h:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=ZMod p) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  by_cases low : B ≤ 2*h+1
  · exact plateau x hk rate length (by omega) even (by omega) (by simpa using budget) low width
  have he : index B h=B/2 := by unfold index ThreeRegimePrimeThreshold.index;split_ifs <;> omega
  have cap := ceiling
  have margin := DoubleQuadraticThreshold.margin_le_five n k
  unfold DoubleQuadraticThreshold.agreements at cap
  rw [he]
  exact DoubleQuadraticThreshold.prime_classification x two (by rw [budget]) (by omega)
    rate large (by omega) (by omega) (by omega) width

/-- The full worst-pair probability on each integer error grid point in the
odd-redundancy interpolation window, for all positive interleavings. -/
theorem mass {p n k h e : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    [ReedSolomon.Smooth x] (large : 65536 ≤ n) (hk : 3 ≤ k) (rate : 3*k ≤ n)
    (length : n=k+2*h-1) (even : n%2=0) (enough : e+DoubleQuadraticThreshold.agreements n k ≤ n)
    (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((if e+1<h then e+1 else if e<h then h+h%2 else min p (2*(e+1)):ℕ):ℝ≥0∞)/p := by
  by_cases low : e+1<h
  · rw [ite_eq_left low,epsMCA_interleaved_eq]
    simpa using OddRedundancyApolar.preunique_mass (e:=e) x hk rate length (by omega) (by omega)
  rw [ite_eq_right low]
  by_cases edge : e<h
  · rw [ite_eq_left edge,epsMCA_interleaved_eq,show e=h-1 by omega]
    simpa using endpoint_mass x hk rate length (by omega) even
  · rw [ite_eq_right edge]
    have cap := enough
    have margin := DoubleQuadraticThreshold.margin_le_five n k
    unfold DoubleQuadraticThreshold.agreements at cap
    exact DoubleQuadraticThreshold.prime_mass x (by omega) rate large (by omega) (by omega) (by omega) width

end ProximityGap.OddSmoothPrimeThreshold
#print axioms ProximityGap.OddSmoothPrimeThreshold.endpoint_mass
#print axioms ProximityGap.OddSmoothPrimeThreshold.exceptional
#print axioms ProximityGap.OddSmoothPrimeThreshold.plateau
#print axioms ProximityGap.OddSmoothPrimeThreshold.classification
#print axioms ProximityGap.OddSmoothPrimeThreshold.mass
