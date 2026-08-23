/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

namespace GradedHtele

/-- The graded per-term telescoping inequality (slack budget form), abstract ℕ:
for non-forbidden `(i₁, σ)` (`¬(i₁ = 0 ∧ σ = 1)`), with `A := D − dH + 1`,
`α := d·A + D + A`, `β := A`:
`(2i₁+σ−2)·(d−1)·A + ((d−σ)·A + (D−σ)) + A·σ ≤ α·(2i₁+σ−1) + β`. -/
theorem graded_htele_arith (d D dH : ℕ)
    (hdH1 : 1 ≤ dH) (hd1 : 1 ≤ d) (hdHD : dH ≤ D)
    (i₁ σ : ℕ) (hσ1 : 1 ≤ σ)
    (hexcl : ¬(i₁ = 0 ∧ σ = 1)) :
    (2 * i₁ + σ - 2) * ((d - 1) * (D - dH + 1))
        + ((d - σ) * (D - dH + 1) + (D - σ))
        + (D - dH + 1) * σ
      ≤ (d * (D - dH + 1) + D + (D - dH + 1)) * (2 * i₁ + σ - 1)
        + (D - dH + 1) := by
  set A := D - dH + 1 with hA
  set k := 2 * i₁ + σ - 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hσk : σ ≤ k + 1 := by omega
  have hkm1 : 2 * i₁ + σ - 2 = k - 1 := by omega
  -- Step 1: weaken LHS: (d−σ) ≤ (d−1) [σ≥1], (D−σ) ≤ D, (k−1)(d−1)A + (d−1)A = k(d−1)A [k≥1]
  have hstep1 : (2 * i₁ + σ - 2) * ((d - 1) * A)
      + ((d - σ) * A + (D - σ)) + A * σ
      ≤ k * ((d - 1) * A) + D + A * σ := by
    rw [hkm1]
    have h1 : (d - σ) * A ≤ (d - 1) * A :=
      Nat.mul_le_mul_right A (Nat.sub_le_sub_left hσ1 d)
    have h2 : D - σ ≤ D := Nat.sub_le D σ
    have h3 : (k - 1) * ((d - 1) * A) + (d - 1) * A = k * ((d - 1) * A) := by
      have : k - 1 + 1 = k := by omega
      calc (k - 1) * ((d - 1) * A) + (d - 1) * A
          = (k - 1 + 1) * ((d - 1) * A) := by ring
        _ = k * ((d - 1) * A) := by rw [this]
    omega
  refine le_trans hstep1 ?_
  -- Step 2: k(d−1)A + D + Aσ ≤ (dA + D + A)·k + A
  -- since k(d−1)A = kdA − kA ≤ kdA, D ≤ kD, Aσ ≤ A(k+1) = kA + A.
  have h4 : k * ((d - 1) * A) ≤ k * (d * A) :=
    Nat.mul_le_mul_left k (Nat.mul_le_mul_right A (Nat.sub_le d 1))
  have h5 : D ≤ k * D := Nat.le_mul_of_pos_left D hk1
  have h6 : A * σ ≤ k * A + A := by
    calc A * σ ≤ A * (k + 1) := Nat.mul_le_mul_left A hσk
      _ = k * A + A := by ring
  calc k * ((d - 1) * A) + D + A * σ
      ≤ k * (d * A) + k * D + (k * A + A) := by omega
    _ = (d * A + D + A) * k + A := by ring

end GradedHtele

#print axioms GradedHtele.graded_htele_arith
