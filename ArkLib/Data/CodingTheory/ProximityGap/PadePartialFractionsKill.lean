/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Round 5 (#357): the Padé partial-fractions kill — the staircase collapse in one line

The Padé bridge (issue record, 2026-06-11) translates the staircase's bad-scalar
configurations into rational-function collinearity: syndromes of block-supported words are
truncations of `P_a/Q_a` with **pairwise coprime** denominators (disjoint supports), and a
bad family makes them affine in γ. Eliminating the line direction through three indices and
clearing denominators yields the polynomial identity treated here:

* `pade_kill` — if `(γ₃−γ₂)·P₁Q₂Q₃ + (γ₁−γ₃)·P₂Q₁Q₃ + (γ₂−γ₁)·P₃Q₁Q₂ = 0` with the `Q`'s
  pairwise coprime, the `γ`'s distinct, and `deg P₁ < deg Q₁`, then `P₁ = 0` — coprimality
  forces `Q₁ ∣ P₁` and the degree bound finishes. *The kernel zeroes a puncture*, in the
  generating-function domain: this is the algebraic heart of the master collapse
  (`MCAStaircaseMaster.collapse_level`), re-proven in one line of commutative algebra.
* `pade_kill_truncated` — the form actually arising from syndromes: the identity holds only
  mod `X^m`; when the combination's degree is `< m` (exactly the `d ≥ 3b−2` regime) the
  congruence upgrades to the exact identity and `pade_kill` applies.

The open strip `2b ≤ d ≤ 3b−3` is the regime where the truncation upgrade fails — the
precise Padé-block-theory question recorded on the tracker.

All results are `sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace ProximityGap.PadePartialFractionsKill

open Polynomial

variable {F : Type} [Field F]

/-- **The partial-fractions kill.** Pairwise-coprime denominators, distinct scalars, and
the exact three-term elimination identity force the first numerator to vanish. -/
theorem pade_kill {P₁ P₂ P₃ Q₁ Q₂ Q₃ : F[X]} {γ₁ γ₂ γ₃ : F}
    (h23 : γ₂ ≠ γ₃)
    (hc12 : IsCoprime Q₁ Q₂) (hc13 : IsCoprime Q₁ Q₃)
    (hdeg : P₁.degree < Q₁.degree)
    (hid : C (γ₃ - γ₂) * (P₁ * (Q₂ * Q₃)) + C (γ₁ - γ₃) * (P₂ * (Q₁ * Q₃))
      + C (γ₂ - γ₁) * (P₃ * (Q₁ * Q₂)) = 0) :
    P₁ = 0 := by
  -- Q₁ divides the last two summands, hence the first
  have hdvd : Q₁ ∣ C (γ₃ - γ₂) * (P₁ * (Q₂ * Q₃)) := by
    have h1 : Q₁ ∣ C (γ₁ - γ₃) * (P₂ * (Q₁ * Q₃)) := ⟨C (γ₁ - γ₃) * (P₂ * Q₃), by ring⟩
    have h2 : Q₁ ∣ C (γ₂ - γ₁) * (P₃ * (Q₁ * Q₂)) := ⟨C (γ₂ - γ₁) * (P₃ * Q₂), by ring⟩
    have h3 : C (γ₃ - γ₂) * (P₁ * (Q₂ * Q₃))
        = -(C (γ₁ - γ₃) * (P₂ * (Q₁ * Q₃))) - (C (γ₂ - γ₁) * (P₃ * (Q₁ * Q₂))) := by
      linear_combination hid
    rw [h3]
    exact dvd_sub (dvd_neg.mpr h1) h2
  -- strip the unit and the coprime factors
  have hne23 : (γ₃ - γ₂) ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
  obtain ⟨u, hu⟩ : IsUnit (C (γ₃ - γ₂)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hne23)
  have hdvd2 : Q₁ ∣ P₁ * (Q₂ * Q₃) := by
    have hstep : Q₁ ∣ (↑u⁻¹ : F[X]) * (C (γ₃ - γ₂) * (P₁ * (Q₂ * Q₃))) :=
      Dvd.dvd.mul_left hdvd _
    have hclear : (↑u⁻¹ : F[X]) * (C (γ₃ - γ₂) * (P₁ * (Q₂ * Q₃)))
        = P₁ * (Q₂ * Q₃) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rwa [hclear] at hstep
  have hcQ : IsCoprime Q₁ (Q₂ * Q₃) := hc12.mul_right hc13
  have hdvd3 : Q₁ ∣ P₁ := by
    have hflip : Q₁ ∣ (Q₂ * Q₃) * P₁ := by rwa [mul_comm]
    exact hcQ.dvd_of_dvd_mul_left hflip
  -- degree kills
  by_contra hP1
  have hQdeg : Q₁.degree ≤ P₁.degree := degree_le_of_dvd hdvd3 hP1
  exact absurd (lt_of_le_of_lt hQdeg hdeg) (lt_irrefl _)

/-- **The truncated form.** When the elimination identity holds only modulo `X^m` but the
combination's degree is `< m` (the `d ≥ 3b−2` regime), the congruence is an exact identity
and the kill applies. -/
theorem pade_kill_truncated {P₁ P₂ P₃ Q₁ Q₂ Q₃ : F[X]} {γ₁ γ₂ γ₃ : F} {m : ℕ}
    (h23 : γ₂ ≠ γ₃)
    (hc12 : IsCoprime Q₁ Q₂) (hc13 : IsCoprime Q₁ Q₃)
    (hdeg : P₁.degree < Q₁.degree)
    (hcomb : (C (γ₃ - γ₂) * (P₁ * (Q₂ * Q₃)) + C (γ₁ - γ₃) * (P₂ * (Q₁ * Q₃))
      + C (γ₂ - γ₁) * (P₃ * (Q₁ * Q₂))).degree < (m : ℕ∞))
    (hmod : (X : F[X]) ^ m ∣ C (γ₃ - γ₂) * (P₁ * (Q₂ * Q₃))
      + C (γ₁ - γ₃) * (P₂ * (Q₁ * Q₃)) + C (γ₂ - γ₁) * (P₃ * (Q₁ * Q₂))) :
    P₁ = 0 := by
  refine pade_kill (γ₁ := γ₁) (P₂ := P₂) (P₃ := P₃) h23 hc12 hc13 hdeg ?_
  by_contra hne
  have hXdeg : ((X : F[X]) ^ m).degree ≤ _ := degree_le_of_dvd hmod hne
  rw [degree_X_pow] at hXdeg
  exact absurd (lt_of_le_of_lt hXdeg hcomb) (lt_irrefl _)

/-! ## Source audit -/

#print axioms pade_kill
#print axioms pade_kill_truncated

end ProximityGap.PadePartialFractionsKill
