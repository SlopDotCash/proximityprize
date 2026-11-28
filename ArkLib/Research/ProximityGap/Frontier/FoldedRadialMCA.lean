/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DrdosDiscriminantBarrier

/-! # Folded radial interpolation at the second-prime Johnson pivots -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.FoldedRadialMCA
open Finset Polynomial

/-- Coefficients of polynomials with plane degree at most s, derivative degree at
most v and strict coordinate-weight bound w. -/
def columns (s v d w : ℕ) : ℕ := ∑ m ∈ range (s + 1),
  (s + 1 - m) * ∑ k ∈ range (min v m + 1), (w + k - d * m)

/-- Local radial jet rows, including the independent scalar coefficients. -/
def rows (s r v : ℕ) : ℕ := ∑ m ∈ range (s + 1),
  (s + 1 - m) * ∑ b ∈ range r, min (r - b) (min v m + 1 - (m - b))

def room (s r v d w : ℕ) : ℕ :=
  columns s v d w - 2 ^ 30 * rows s r v

set_option maxRecDepth 8192 in
/-- The two smaller boards capture jets. The larger boards leave enough coordinate
weight to differentiate in both directions which preserve the received line. -/
theorem pivots :
    room 99 19 6 536870911 14425752375 = 4128454092 ∧
    room 63 11 5 268435455 5905580021 = 17888 ∧
    room 359 73 24 536870911 54888388213 = 459712885250 ∧
    room 269 55 26 268435455 28722593737 = 729614679390 ∧
    room 453 57 15 536870911 42740386213 = 193772302476 ∧
    room 333 44 17 268435455 22817013716 = 285082020609 := by decide +kernel

set_option maxRecDepth 8192 in
/-- Two additional ordinary boards restrict all fixed differential surfaces to
derivative degree at most two. The mixed curve cuts give the stated populations. -/
theorem quadratic_derivative_caps :
    room 292 15 2 536870911 (15 * 759250125) = 1603007627 ∧
    room 167 9 2 268435455 (9 * 536870911) = 1610623611 ∧
    2 ^ 31 + 1 - (99 * 359 ^ 2 + 4386 ^ 2 + 99 * 359) = (2115451893 : ℕ) ∧
    2 ^ 31 + 1 - (63 * 269 ^ 2 + 2853 ^ 2 + 63 * 269) = (2134768350 : ℕ) := by
  decide +kernel

/-- The two folding deformations and the derivative-coordinate jet force
ordinary singularity whenever the received fold differs from the witness polynomial. -/
theorem gradient_zero {F : Type*} [Field F] (a b c u v w z : F)
    (hv : v = 0) (hw : w ≠ 0) (shear : z + a * u + b * v = 0)
    (scale : w * u + c * v = 0) : z = 0 ∧ u = 0 ∧ v = 0 := by
  rw [hv, mul_zero, add_zero] at scale
  have hu := (mul_eq_zero.mp scale).resolve_left hw
  simpa [hu, hv] using shear

/-- The logarithmic derivatives of two residuals distinguish their scalar labels
when the received rows are independent modulo the degree bound. -/
theorem labels_of_wronskian {F : Type*} [Field F] {w d : ℕ}
    (hchar : ringChar F = 0 ∨ w < ringChar F) (u v q₁ q₂ : F[X]) (z₁ z₂ : F)
    (hq₁ : q₁.natDegree ≤ d) (hq₂ : q₂.natDegree ≤ d)
    (independent : ∀ a b : F, (C a * u + C b * v).natDegree ≤ d → a = 0 ∧ b = 0)
    (r₁ : q₁ - u - C z₁ * v ≠ 0)
    (hd₁ : (q₁ - u - C z₁ * v).natDegree ≤ w)
    (hd₂ : (q₂ - u - C z₂ * v).natDegree ≤ w)
    (hW : (q₁ - u - C z₁ * v).derivative * (q₂ - u - C z₂ * v) =
      (q₁ - u - C z₁ * v) * (q₂ - u - C z₂ * v).derivative) : z₁ = z₂ := by
  obtain ⟨c, hc⟩ := DrdosDiscriminantBarrier.wronskian_eq_zero_implies_scalar_mul
    hchar r₁ hd₁ hd₂ hW
  have eq : C (1 - c) * u + C (z₂ - c * z₁) * v = q₂ - C c * q₁ := by
    simp only [map_sub, map_one, map_mul]
    linear_combination -hc
  have hlow := (natDegree_sub_le q₂ (C c * q₁)).trans
    (max_le hq₂ ((natDegree_C_mul_le _ _).trans hq₁))
  rw [← eq] at hlow
  obtain ⟨one, two⟩ := independent _ _ hlow
  have hc₁ : c = 1 := (sub_eq_zero.mp one).symm
  simpa [hc₁] using (sub_eq_zero.mp two).symm

#print axioms pivots
#print axioms quadratic_derivative_caps
#print axioms gradient_zero
#print axioms labels_of_wronskian
end ArkLib.ProximityGap.Frontier.FoldedRadialMCA
