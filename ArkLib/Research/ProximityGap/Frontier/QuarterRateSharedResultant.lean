/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateRichSecants
import ArkLib.Research.ProximityGap.Frontier.WeightedSylvesterDegree

/-! # The two quarter-rate interpolants have a common factor over the function field

For a family exceeding the first prime's budget, the resultant in the value
variable of the actual two interpolants vanishes. Its scalar degree is below
the number of distinct selected scalar labels. The determinant uses the two
actual value degrees, so padding cannot force it to vanish.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterRateSharedResultant
open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge
open scoped NNReal

private theorem shape {F : Type} [Field F] {s v d t : ℕ} (c : Monomials s v d t → F) :
    (surface c).natDegree ≤ v ∧ WeightedSylvesterDegree.TotalDegreeLe (surface c) s := by
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support c h).1
  · intro j hj
    let P := (surface c).coeff j
    have hi : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hj
    have ha : (P.coeff P.natDegree).coeff (P.coeff P.natDegree).natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hi
    exact (surface_support c ha).2.1

variable {F I : Type} [Field F] [DecidableEq F] [Fintype I]

/-- A bad family with more than $2^{30}$ labels forces a zero resultant for
two nonzero surfaces of value degrees at most two and three. -/
theorem common_resultant {D : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily D 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : 626349397 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) (hG : 1073741824 < fam.G.card) :
    ∃ (a : Monomials 268435458 2 268435455 626349397 → F)
      (b : Monomials 16 3 268435455 (2 * 626349397) → F), a ≠ 0 ∧ b ≠ 0 ∧
      (∀ z ∈ fam.G, specialize a z (fam.q z) = 0 ∧ specialize b z (fam.q z) = 0) ∧
      resultant (surface a) (surface b) (surface a).natDegree (surface b).natDegree = 0 := by
  classical
  obtain ⟨a, b, ha, hb, hr⟩ := QuarterRateRichSecants.shared_equations fam hn ht
  refine ⟨a, b, ha, hb, hr, ?_⟩
  obtain ⟨ya, ta⟩ := shape a
  obtain ⟨yb, tb⟩ := shape b
  have distinct : Function.Injective (fun z : fam.G => (C (z : F) : F[X])) :=
    C_injective.comp Subtype.val_injective
  have posa : (surface a).natDegree ≠ 0 := by
    intro hz
    have hQ := eq_C_of_natDegree_eq_zero hz
    have hc : (surface a).coeff 0 ≠ 0 := by
      intro h
      exact surface_ne_zero ha (hQ.trans (by rw [h, C_0]))
    apply hc
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ distinct
    · intro z
      have h := (hr z z.property).1
      rw [← surface_eval] at h
      nth_rw 1 [hQ] at h
      simpa only [eval₂_C, coe_evalRingHom] using h
    · have h := ta 0 hc
      rw [Fintype.card_coe]
      omega
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ distinct
  · intro z
    have ⟨h₁, h₂⟩ := hr z z.property
    apply map_resultant_eq_zero_of_common_root (evalRingHom (C (z : F))) _ _
      le_rfl le_rfl (.inl posa) (fam.q z)
    · simpa only [eval_map, surface_eval] using h₁
    · simpa only [eval_map, surface_eval] using h₂
  · have hd := WeightedSylvesterDegree.natDegree_resultant_le (surface a) (surface b)
      (b := (surface a).natDegree) (b' := (surface b).natDegree) ta tb
    rw [Fintype.card_coe]
    omega

end ArkLib.ProximityGap.Frontier.QuarterRateSharedResultant
