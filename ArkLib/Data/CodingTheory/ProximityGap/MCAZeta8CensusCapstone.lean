/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeta8CensusCheck

/-!
# The `n = 8` census capstone (#357): the per-instance classification theorem

Extraction plumbing for the kernel sweep `census8_check`: the per-instance statement
that, for every canonical admissible pair-triangle of `μ₈`,

* `census8_complete` — the integer determinant vanishes **iff** the triangle is of
  classified (horizontal/vertical/slanted) form;
* `mu8_collinear_iff_classified` — the same as a **field-level** statement: over any
  `CharZero` field with a primitive 8th root, the collinearity determinant of the
  pair-points vanishes iff the triangle is classified.

This closes the census-by-computation arc at `n = 8`: pencil criterion (any field) →
coordinate bridge (char 0) → kernel census (absolute) → **per-instance classification**
(this file). The transfer of the classification to finite fields below the char-0
thresholds remains the named norm-threshold surface (measured: the mod-`97` census at
`n = 16` already carries 384 spurious coincidences).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeta8Census

/-- **The per-instance census theorem.** For canonical admissible tuples, the integer
collinearity determinant vanishes iff the triangle is of classified form. -/
theorem census8_complete {p p' q q' r r' : ℕ}
    (hcan : canonicalB p p' q q' r r' = true) :
    detVec p p' q q' r r' = Z8.zero ↔ classifiedB p p' q q' r r' = true := by
  have hb : p < 8 ∧ p' < 8 ∧ q < 8 ∧ q' < 8 ∧ r < 8 ∧ r' < 8 := by
    have hc := hcan
    simp only [canonicalB, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hc
    omega
  have h := census8_check
  unfold censusOK at h
  rw [List.all_eq_true] at h
  have h1 := h p (List.mem_range.mpr hb.1)
  simp only [List.all_eq_true] at h1
  have h2 := h1 p' (List.mem_range.mpr hb.2.1)
  simp only [List.all_eq_true] at h2
  have h3 := h2 q (List.mem_range.mpr hb.2.2.1)
  simp only [List.all_eq_true] at h3
  have h4 := h3 q' (List.mem_range.mpr hb.2.2.2.1)
  simp only [List.all_eq_true] at h4
  have h5 := h4 r (List.mem_range.mpr hb.2.2.2.2.1)
  simp only [List.all_eq_true] at h5
  have h6 := h5 r' (List.mem_range.mpr hb.2.2.2.2.2)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h6
  rcases h6 with hfalse | heq
  · rw [hcan] at hfalse
    cases hfalse
  · rw [beq_iff_eq] at heq
    constructor
    · intro hz
      rw [← heq]
      exact decide_eq_true hz
    · intro hc
      have hd : decide (detVec p p' q q' r r' = Z8.zero) = true := by
        rw [heq]
        exact hc
      exact of_decide_eq_true hd

section Field

variable {L : Type*} [Field L] [CharZero L]

/-- **The field-level classification.** Over any `CharZero` field with a primitive 8th
root: the collinearity determinant of a canonical `μ₈` pair-triangle vanishes iff the
triangle is horizontal, vertical, or slanted. The complete `n = 8` wide-circuit census
as a single statement. -/
theorem mu8_collinear_iff_classified {ζ : L} (hζ : IsPrimitiveRoot ζ 8)
    {p p' q q' r r' : ℕ} (hcan : canonicalB p p' q q' r r' = true) :
    (((ζ ^ q + ζ ^ q') - (ζ ^ p + ζ ^ p')) * (ζ ^ (r + r') - ζ ^ (p + p'))
      - (ζ ^ (q + q') - ζ ^ (p + p')) * ((ζ ^ r + ζ ^ r') - (ζ ^ p + ζ ^ p')) = 0)
    ↔ classifiedB p p' q q' r r' = true := by
  rw [collinear_iff_detVec_eq_zero hζ]
  exact census8_complete hcan

end Field

/-! ## Source audit -/

#print axioms census8_complete
#print axioms mu8_collinear_iff_classified

end ProximityGap.MCAZeta8Census
