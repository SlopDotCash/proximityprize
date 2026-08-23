/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136AnchorConstantSharp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# G136 (part 1): the unit-circle Mann classification — four-term sums, elementary

The accident reduction needs the characteristic-zero classification of solutions to
`a + b = c + 1` among roots of unity.  Cyclotomic-tower induction is unnecessary: the
conjugate trick gives a fully elementary, fully general classification for ARBITRARY
unit-modulus complex numbers:

conjugating the equation turns it into `a⁻¹ + b⁻¹ = c⁻¹ + 1`; clearing denominators against
the original yields `(c + 1)·(c − a·b) = 0`, and in the branch `c = a·b` the original
equation factors as `(a − 1)·(b − 1) = 0`.  Hence

```text
a + b = c + 1  ⟹  a = 1 ∨ b = 1 ∨ (c = −1 ∧ b = −a).
```

These are exactly the identity/swap families and the zero-sum plane of part 0 — so in
characteristic zero the three families are EVERYTHING, for roots of unity of every order
simultaneously.  Every further mod-`p` solution is a genuine reduction accident (part 2/3:
the accident law and the sharp per-prime criterion).

**Honest scope.**  Characteristic-zero classification; the transfer to `ZMod p` and the
production criterion are the remaining parts.  CORE remains OPEN.  Issue #466 (G136).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G136UnitCircleMann

open Complex

/-- **The unit-circle Mann classification.**  For unit-modulus `a, b, c`, the only solutions
of `a + b = c + 1` are the diagonal families and the zero-sum plane. -/
theorem unit_sum_classification {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (h : a + b = c + 1) :
    a = 1 ∨ b = 1 ∨ (c = -1 ∧ b = -a) := by
  have hane : a ≠ 0 := fun h0 => by simp [h0] at ha
  have hbne : b ≠ 0 := fun h0 => by simp [h0] at hb
  have hcne : c ≠ 0 := fun h0 => by simp [h0] at hc
  -- conjugate the equation
  have hconj : a⁻¹ + b⁻¹ = c⁻¹ + 1 := by
    have := congrArg (starRingEnd ℂ) h
    simpa [map_add, ← Complex.inv_eq_conj ha, ← Complex.inv_eq_conj hb,
      ← Complex.inv_eq_conj hc] using this
  -- clear denominators: (a + b)·c = (c + 1)·(a·b)
  have hcleared : (a + b) * c = (c + 1) * (a * b) := by
    have h1 : (a⁻¹ + b⁻¹) * (a * b * c) = (c⁻¹ + 1) * (a * b * c) := by
      rw [hconj]
    field_simp at h1
    linear_combination h1
  -- substitute the original equation: (c + 1)·(c − a·b) = 0
  have hkey : (c + 1) * (c - a * b) = 0 := by
    have : (c + 1) * c = (c + 1) * (a * b) := by
      calc
        (c + 1) * c = (a + b) * c := by rw [h]
        _ = (c + 1) * (a * b) := hcleared
    linear_combination this
  rcases mul_eq_zero.mp hkey with hc1 | hab
  · -- c = −1: zero-sum plane
    have hcm1 : c = -1 := by linear_combination hc1
    right; right
    refine ⟨hcm1, ?_⟩
    have : a + b = 0 := by
      rw [hcm1] at h
      linear_combination h
    linear_combination this
  · -- c = a·b: diagonal factorization (a − 1)(b − 1) = 0
    have hcab : c = a * b := by linear_combination hab
    have hfact : (a - 1) * (b - 1) = 0 := by
      rw [hcab] at h
      linear_combination -h
    rcases mul_eq_zero.mp hfact with h1 | h1
    · left; linear_combination h1
    · right; left; linear_combination h1

end ArkLib.ProximityGap.Frontier.G136UnitCircleMann

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G136UnitCircleMann.unit_sum_classification
