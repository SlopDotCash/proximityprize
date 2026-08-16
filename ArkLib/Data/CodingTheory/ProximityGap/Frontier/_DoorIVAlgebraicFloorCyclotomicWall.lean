import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Door-IV algebraic-floor cyclotomic wall

This file kernel-anchors the concrete obstruction exposed by
`scripts/probes/probe_algebraic_floor_cyclotomic_wall.py`.

The proposed algebraic-floor / higher-order-MDS route needs gapped Vandermonde minors on
cyclotomic rows to be generically nonzero.  In the dyadic prize object this already fails at
`μ₁₆`: the `3 × 3` minor with row exponents `(1,2,5)` and column powers `(1,5,9)` vanishes
whenever `ζ^8 = -1`.  The adjacent contiguous Vandermonde control is deliberately not used here;
the point is the exact cyclotomic relation in the gapped minor.

No CORE/cancellation/completion/moment/capacity claim is made.
-/

namespace ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall

/-- The determinant of a `3 × 3` matrix, written out to keep this obstruction dependency-free. -/
def det3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℂ) : ℂ :=
  a11 * (a22 * a33 - a23 * a32)
    - a12 * (a21 * a33 - a23 * a31)
    + a13 * (a21 * a32 - a22 * a31)

/-- The concrete gapped cyclotomic minor from rows `(1,2,5)` and powers `(1,5,9)`. -/
def gappedMinor125_159 (ζ : ℂ) : ℂ :=
  det3
    (ζ ^ 1)  (ζ ^ 5)  (ζ ^ 9)
    (ζ ^ 2)  (ζ ^ 10) (ζ ^ 18)
    (ζ ^ 5)  (ζ ^ 25) (ζ ^ 45)

/--
**Cyclotomic wall for the algebraic-floor route.**  At a dyadic sixteenth root with `ζ^8 = -1`,
the explicit gapped `3 × 3` minor `(rows 1,2,5; powers 1,5,9)` vanishes.

Thus a proof that requires all such gapped minors on `μ₂ᵃ` to be nonzero cannot be discharged by
plain Dirichlet/generic-MDS reasoning; it has to confront the cyclotomic vanishing relations.
-/
theorem gappedMinor125_159_eq_zero_of_pow8_eq_neg_one {ζ : ℂ} (hζ : ζ ^ 8 = -1) :
    gappedMinor125_159 ζ = 0 := by
  unfold gappedMinor125_159 det3
  have h16 : ζ ^ 16 = 1 := by
    calc
      ζ ^ 16 = (ζ ^ 8) ^ 2 := by ring
      _ = (-1 : ℂ) ^ 2 := by rw [hζ]
      _ = 1 := by norm_num
  have h9 : ζ ^ 9 = -ζ := by
    calc
      ζ ^ 9 = ζ * ζ ^ 8 := by ring
      _ = ζ * (-1 : ℂ) := by rw [hζ]
      _ = -ζ := by ring
  have h10 : ζ ^ 10 = -(ζ ^ 2) := by
    calc
      ζ ^ 10 = ζ ^ 2 * ζ ^ 8 := by ring
      _ = ζ ^ 2 * (-1 : ℂ) := by rw [hζ]
      _ = -(ζ ^ 2) := by ring
  have h18 : ζ ^ 18 = ζ ^ 2 := by
    calc
      ζ ^ 18 = ζ ^ 2 * ζ ^ 16 := by ring
      _ = ζ ^ 2 * 1 := by rw [h16]
      _ = ζ ^ 2 := by ring
  have h25 : ζ ^ 25 = -ζ := by
    calc
      ζ ^ 25 = ζ * (ζ ^ 8) ^ 3 := by ring
      _ = ζ * (-1 : ℂ) ^ 3 := by rw [hζ]
      _ = -ζ := by ring
  have h45 : ζ ^ 45 = -(ζ ^ 5) := by
    calc
      ζ ^ 45 = ζ ^ 5 * (ζ ^ 8) ^ 5 := by ring
      _ = ζ ^ 5 * (-1 : ℂ) ^ 5 := by rw [hζ]
      _ = -(ζ ^ 5) := by ring
  have h12 : ζ ^ 12 = -(ζ ^ 4) := by
    calc
      ζ ^ 12 = ζ ^ 4 * ζ ^ 8 := by ring
      _ = ζ ^ 4 * (-1 : ℂ) := by rw [hζ]
      _ = -(ζ ^ 4) := by ring
  rw [h9, h10, h18, h25, h45]
  ring_nf
  rw [h12]
  ring

/-- A generic nonvanishing hypothesis on the same gapped minor contradicts the dyadic relation. -/
theorem not_gappedMinor125_159_ne_zero_of_pow8_eq_neg_one {ζ : ℂ} (hζ : ζ ^ 8 = -1) :
    ¬ gappedMinor125_159 ζ ≠ 0 := by
  intro hne
  exact hne (gappedMinor125_159_eq_zero_of_pow8_eq_neg_one hζ)

#print axioms gappedMinor125_159_eq_zero_of_pow8_eq_neg_one
#print axioms not_gappedMinor125_159_ne_zero_of_pow8_eq_neg_one

end ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall
