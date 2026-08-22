/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G82TransversalityCRTThreshold

/-!
# G83: determinant coverage fence at the support-six threshold

G82 isolated the remaining transversality input as common vanishing at many distinct
degree-one primes.  The documented prize-cell instantiation uses a full-rank integer census
matrix: common coverage makes `p^s` divide its nonzero determinant, while the support-six
Hadamard estimate gives `D^2 ≤ 6^d` in rank `d`.

This file proves the exact arithmetic handoff.  Those two certificates force

`p^(2s) ≤ 6^d`, and hence `s * log p ≤ (d/2) * log 6`.

Thus coverage strictly above the half-height threshold contradicts any such determinant
certificate.  The geometric step producing the determinant and its squared Hadamard bound from
the actual cyclotomic census rows is deliberately an explicit hypothesis here; it remains the
open prize-facing bridge.  No bound on `M` is claimed.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G83DeterminantCoverageFence

/-- The two integer facts supplied by a full-rank support-six census matrix: common coverage
divides its positive determinant, and Hadamard bounds the determinant square. -/
structure SupportSixDeterminantCertificate (p s d determinant : ℕ) : Prop where
  determinant_pos : 0 < determinant
  coverage_dvd : p ^ s ∣ determinant
  hadamard_sq : determinant ^ 2 ≤ 6 ^ d

/-- Common coverage and the squared Hadamard certificate amplify to the exact squared CRT bound. -/
theorem pow_two_mul_coverage_le
    {p s d determinant : ℕ} (h : SupportSixDeterminantCertificate p s d determinant) :
    p ^ (2 * s) ≤ 6 ^ d := by
  have hle : p ^ s ≤ determinant := Nat.le_of_dvd h.determinant_pos h.coverage_dvd
  have hsq : (p ^ s) ^ 2 ≤ determinant ^ 2 := Nat.pow_le_pow_left hle 2
  calc
    p ^ (2 * s) = (p ^ s) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ determinant ^ 2 := hsq
    _ ≤ 6 ^ d := h.hadamard_sq

/-- The determinant certificate gives the half-height logarithmic coverage fence. -/
theorem coverage_log_le_half_height
    {p s d determinant : ℕ} (hp : 2 ≤ p)
    (h : SupportSixDeterminantCertificate p s d determinant) :
    (s : ℝ) * Real.log p ≤ (d : ℝ) / 2 * Real.log 6 := by
  have hlog :=
    G82TransversalityCRTThreshold.coverage_log_bound
      p (6 ^ d) (2 * s) hp (by exact Nat.one_le_pow d 6 (by norm_num))
      (pow_two_mul_coverage_le h)
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Real.log_pow] at hlog
  calc
    (s : ℝ) * Real.log p = (2 * (s : ℝ) * Real.log p) / 2 := by ring
    _ ≤ ((d : ℝ) * Real.log 6) / 2 :=
      div_le_div_of_nonneg_right hlog (by norm_num)
    _ = (d : ℝ) / 2 * Real.log 6 := by ring

/-- Coverage strictly beyond the half-height threshold rules out a support-six determinant
certificate.  This is the precise fence-side contradiction consumed by G82. -/
theorem no_certificate_above_half_height
    {p s d : ℕ} (hp : 2 ≤ p)
    (hlarge : (d : ℝ) / 2 * Real.log 6 < (s : ℝ) * Real.log p) :
    ∀ determinant, ¬ SupportSixDeterminantCertificate p s d determinant := by
  intro determinant
  intro h
  exact (not_le_of_gt hlarge) (coverage_log_le_half_height hp h)

end ArkLib.ProximityGap.Frontier.G83DeterminantCoverageFence

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G83DeterminantCoverageFence.pow_two_mul_coverage_le
#print axioms
  ArkLib.ProximityGap.Frontier.G83DeterminantCoverageFence.coverage_log_le_half_height
#print axioms
  ArkLib.ProximityGap.Frontier.G83DeterminantCoverageFence.no_certificate_above_half_height
