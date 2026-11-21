import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Divisibility and chord estimates for the dyadic Gauss-period upper bound

The full determinant proof is recorded in the shared research log. This file checks
the rank-one column divisibility argument, the archimedean chord inequality and
the two production integer comparisons used there.
-/

namespace ProximityGap.Frontier.DyadicPeriodCeiling

open Finset Matrix

/-- If every column indexed by s is proportional modulo m to an anchor
outside s, the determinant contains at least one factor of m per column. -/
theorem pow_dvd_det_of_columns {I : Type*} [Fintype I] [DecidableEq I]
    (anchor : I) (m : ℤ) (s : Finset I) (A : Matrix I I ℤ) (ha : anchor ∉ s)
    (hc : ∀ j ∈ s, ∃ (c : ℤ) (u : I → ℤ), ∀ i, A i j = c * A i anchor + m * u i) :
    m ^ s.card ∣ A.det := by
  induction s using Finset.induction_on generalizing A with
  | empty => simp
  | @insert j s hj ih =>
    have hja : j ≠ anchor := by
      rintro rfl
      exact ha (mem_insert_self _ _)
    obtain ⟨c, u, hu⟩ := hc j (mem_insert_self _ _)
    let B := A.updateCol j u
    have heq : A.det = m * B.det := by
      rw [← A.det_updateCol_add_smul_self hja (-c), ← A.det_updateCol_smul j m u]
      apply congrArg Matrix.det
      apply congrArg (A.updateCol j)
      funext i
      simp only [smul_eq_mul, Pi.smul_apply, hu]
      ring
    have htail : m ^ s.card ∣ B.det := by
      apply ih B (fun h => ha (mem_insert_of_mem h))
      intro v hv
      obtain ⟨a, w, hw⟩ := hc v (mem_insert_of_mem hv)
      refine ⟨a, w, fun i => ?_⟩
      have hvj : v ≠ j := by
        rintro rfl
        exact hj hv
      simpa only [B, updateCol_ne hvj, updateCol_ne hja.symm] using hw i
    obtain ⟨z, hz⟩ := htail
    rw [card_insert_of_notMem hj, pow_succ, heq, hz]
    exact ⟨z, by ring⟩

/-- The chord estimate, with the phase normalized to a full turn. -/
theorem chord_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    8 * x ^ 2 ≤ 1 - Real.cos (2 * (Real.pi * x)) := by
  have hpi := Real.pi_pos
  have hπ : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith [mul_le_mul_of_nonneg_left hx hpi.le]
  have hmain := Real.mul_abs_le_abs_sin hπ
  rw [abs_mul, abs_of_pos hpi] at hmain
  have hs : (2 * |x|) ^ 2 ≤ |Real.sin (Real.pi * x)| ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    convert hmain using 1
    field_simp
  rw [mul_pow, sq_abs, sq_abs] at hs
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*x)]

theorem first_prime_root_certificate :
    (14184505 : ℕ) ^ 128 * (2 * 365375409332725729550921208179070755120141565953) <
      (2 ^ 25) ^ 128 := by decide +kernel

theorem second_prime_root_certificate :
    (14107900 : ℕ) ^ 128 * (2 * 730750818665451459101842416358141509841924915201) <
      (2 ^ 25) ^ 128 := by decide +kernel

#print axioms pow_dvd_det_of_columns
#print axioms chord_bound
#print axioms first_prime_root_certificate
#print axioms second_prime_root_certificate

end ProximityGap.Frontier.DyadicPeriodCeiling
