/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungAgreementGeometry

/-!
# The rung frame census (#371, round-7 target): the off-agreement disjointness

The counting heart of the level-1 rung's good side.  Once a bad scalar is
"attached" to an agreement set `A` of the direction row (`R₁ − q = m_A·h`)
with frame `r` (`P = r + γq`), its defect identity shifts to
`(R₀ − r) + γ·m_A·h = g·m_S`.  Subtracting two such identities and evaluating:

* **`frame_cross_disjoint`** — witnesses of DISTINCT attached scalars meet
  only inside `A ∪ roots(h)`: off the agreement set (and off the `h`-locus),
  the witnesses are pairwise disjoint;
* `vanishingPoly_eval_eq_zero_iff` — the root/membership dictionary;
* **`disjoint_offparts_card_le`** — the count: any family of scalars with
  pairwise-disjoint nonempty "off-parts" inside a finite reservoir is at most
  the reservoir's size.

At the rung instance the reservoir is `D ∖ A` (8 points) plus the single
`h`-root: per (A, frame) at most 9 attached scalars — the probe-exact value is
8 per half-coset, a perfect matching with the rotating cross-points
(`probe_wb371_rung_offA`-record: 0 law violations over 504 pairs, off-parts
singletons, bijective).  Two half-cosets × 8 + zero-class = the pencil's 17;
the assembly toward the obligation `≤ 31` proceeds per agreement-set sizes.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The root/membership dictionary for vanishing polynomials. -/
theorem vanishingPoly_eval_eq_zero_iff (dom : Fin n ↪ F)
    {T : Finset (Fin n)} {i : Fin n} :
    (vanishingPoly dom T).eval (dom i) = 0 ↔ i ∈ T := by
  constructor
  · intro h
    rw [vanishingPoly, eval_prod, Finset.prod_eq_zero_iff] at h
    obtain ⟨j, hj, hij⟩ := h
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hij
    exact dom.injective hij ▸ hj
  · exact vanishingPoly_eval_eq_zero dom

section FrameCensus

variable {dom : Fin n ↪ F}
variable {R₀' h : F[X]}

/-- **The off-agreement disjointness law.**  Witnesses of distinct attached
scalars meet only inside the agreement set or the `h`-locus. -/
theorem frame_cross_disjoint
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) {g₁ g₂ : F[X]} {A S₁ S₂ : Finset (Fin n)}
    (hid₁ : R₀' + C γ₁ * (vanishingPoly dom A * h)
      = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀' + C γ₂ * (vanishingPoly dom A * h)
      = g₂ * vanishingPoly dom S₂) :
    ∀ i ∈ S₁ ∩ S₂, i ∈ A ∨ h.eval (dom i) = 0 := by
  intro i hi
  rw [Finset.mem_inter] at hi
  have hev₁ := congrArg (Polynomial.eval (dom i)) hid₁
  have hev₂ := congrArg (Polynomial.eval (dom i)) hid₂
  rw [eval_mul, vanishingPoly_eval_eq_zero dom hi.1, mul_zero] at hev₁
  rw [eval_mul, vanishingPoly_eval_eq_zero dom hi.2, mul_zero] at hev₂
  simp only [eval_add, eval_mul, eval_C] at hev₁ hev₂
  -- subtract: (γ₁ − γ₂) · m_A(x) · h(x) = 0
  have hkey : (γ₁ - γ₂) * ((vanishingPoly dom A).eval (dom i)
      * h.eval (dom i)) = 0 := by
    linear_combination hev₁ - hev₂
  have hγ : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  rcases mul_eq_zero.mp hkey with hc | hprod
  · exact absurd hc hγ
  · rcases mul_eq_zero.mp hprod with hA | hh
    · exact Or.inl ((vanishingPoly_eval_eq_zero_iff dom).mp hA)
    · exact Or.inr hh

/-- **The disjoint off-parts count**: a family of scalars with pairwise
disjoint nonempty off-parts inside a reservoir is no larger than the
reservoir. -/
theorem disjoint_offparts_card_le {Γ : Finset F} {W : Finset (Fin n)}
    (off : F → Finset (Fin n))
    (hsub : ∀ γ ∈ Γ, off γ ⊆ W)
    (hne : ∀ γ ∈ Γ, (off γ).Nonempty)
    (hdisj : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → Disjoint (off γ₁) (off γ₂)) :
    Γ.card ≤ W.card := by
  classical
  have hcard : Γ.card ≤ (Γ.biUnion off).card := by
    rw [Finset.card_biUnion hdisj]
    calc Γ.card = ∑ _γ ∈ Γ, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ γ ∈ Γ, (off γ).card :=
          Finset.sum_le_sum fun γ hγ => Finset.card_pos.mpr (hne γ hγ)
  refine le_trans hcard (Finset.card_le_card ?_)
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨γ, hγ, hxγ⟩ := hx
  exact hsub γ hγ hxγ

end FrameCensus

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.vanishingPoly_eval_eq_zero_iff
#print axioms ProximityGap.WBPencil.frame_cross_disjoint
#print axioms ProximityGap.WBPencil.disjoint_offparts_card_le
