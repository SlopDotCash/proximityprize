/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarAllFieldPlateau
import ArkLib.Research.ProximityGap.Frontier.DoubleQuadraticThreshold

/-! # Finite prime-field threshold from the zero budget through the two-head region

At even redundancy and rate strictly below one third the spike, the
half-distance plateau and the two-head regime meet. This covers the three
lower prize rates on dyadic domains of length at least 65536.
-/
set_option autoImplicit false
namespace ProximityGap.ThreeRegimePrimeThreshold
open MCAThresholdLedger ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal

/-- The first failing count for budget B when half the redundancy is h. -/
def index (B h : ℕ) := min B (max h (B/2))

/-- For all positive widths, the sharp real threshold and the full good interval
are given by one integer expression on the indicated budget interval. -/
theorem classification {p n k h B Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (large : 65536≤n) (hk : 2≤k) (length : k+2*h=n) (rate : n<3*h)
    (two : 2≤Q) (budget : p/Q=B) (ceiling : B/2 + DoubleQuadraticThreshold.agreements n k ≤ n+1)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let b := ((index B h:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/(Q:ℝ≥0∞)) = b ∧
      ∀ δ, epsMCA (F:=ZMod p) C δ≤1/(Q:ℝ≥0∞) ↔ δ<b := by
  by_cases low : B ≤ 2*h+1
  · have he : index B h=min B h := by unfold index;omega
    have result := ApolarAllFieldPlateau.classification x hk (by rwa [Fintype.card_fin])
      (by rwa [Fintype.card_fin]) (by omega : 0<Q) (by simpa only [ZMod.card] using budget) low width
    simpa only [Fintype.card_fin,he] using result
  · have he : index B h=B/2 := by unfold index;omega
    have marginBound := DoubleQuadraticThreshold.margin_le_five n k
    have room := ceiling
    unfold DoubleQuadraticThreshold.agreements at room
    have result := DoubleQuadraticThreshold.prime_classification (k:=k) (j:=B/2) x two
      (by rw [budget]) hk (by omega) large (by omega) (by omega) (by omega) width
    simpa only [he] using result

/-- At integer errors the exact bad probability itself has the spike numerator
below half-redundancy, and the saturated two-head numerator from that step
onward while the variable-degree interpolation bound applies. -/
theorem mass_unconditional {p n k h e : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (large : 65536≤n) (hk : 2≤k) (length : k+2*h=n) (rate : n<3*h)
    (enough : e + DoubleQuadraticThreshold.agreements n k ≤ n)
    (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((if e<h then e+1 else min p (2*(e+1)) : ℕ):ℝ≥0∞)/p := by
  rw [epsMCA_interleaved_eq]
  by_cases low : e<h
  · rw [if_pos low]
    simpa only [Fintype.card_fin,ZMod.card] using ApolarAllFieldPlateau.preunique_mass (e:=e) x hk
      (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin]) low
  · rw [if_neg low]
    have marginBound := DoubleQuadraticThreshold.margin_le_five n k
    have room := enough
    unfold DoubleQuadraticThreshold.agreements at room
    have result := DoubleQuadraticThreshold.prime_mass (e:=e) x hk (by omega)
      large (by omega) (by omega) (by omega) width
    simpa only [epsMCA_interleaved_eq] using result

/-- Compatibility form with the original characteristic hypothesis. -/
theorem mass {p n k h e : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (large : 65536≤n) (hk : 2≤k) (length : k+2*h=n) (rate : n<3*h)
    (enough : e + DoubleQuadraticThreshold.agreements n k ≤ n)
    (_field : e<h ∨ 2*(n-e-1)<p) (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((if e<h then e+1 else min p (2*(e+1)) : ℕ):ℝ≥0∞)/p :=
  mass_unconditional x large hk length rate enough width

end ProximityGap.ThreeRegimePrimeThreshold
#print axioms ProximityGap.ThreeRegimePrimeThreshold.classification
#print axioms ProximityGap.ThreeRegimePrimeThreshold.mass
#print axioms ProximityGap.ThreeRegimePrimeThreshold.mass_unconditional
