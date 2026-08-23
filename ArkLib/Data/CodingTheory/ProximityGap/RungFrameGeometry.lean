/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungMaximalFrame

/-!
# Rung frame geometry (#371): frame determination and the pencil-root cap

The two laws behind the block-frame census campaign's caps (record 22,
`probe_wb371_blockframe*.py`):

* `attached_R0_agrees_frame_on_A` — on `S ∩ A` (witness meets agreement
  set), the row `R₀` agrees with the scalar's frame `P − γq`: frames are
  `R₀`-interpolants, so witnesses sharing ≥ k points of `A` share frames;
* `cross_frame_inter_le` — witnesses of scalars with DISTINCT frames meet
  in fewer than `k` points inside `A`;
* `pencil_degenerate_of_roots` — the pencil-root cap: a deg `< k` pencil
  member vanishing at `k` domain points is the zero member, forcing the
  full degeneration `R = C γ * Q` (the `q`-collapse that kills every
  ladder escalation past 2 small scalars).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section FrameGeometry

variable {dom : Fin n ↪ F} {k : ℕ} {R₀ R₁ q : F[X]}

/-- **Frame determination**: where a witness meets an agreement set of the
direction row, `R₀` agrees with the frame `P − C γ * q`. -/
theorem attached_R0_agrees_frame_on_A
    {γ : F} {P g : F[X]} {A S : Finset (Fin n)}
    (hA : ∀ i ∈ A, R₁.eval (dom i) = q.eval (dom i))
    (hid : R₀ + C γ * R₁ - P = g * vanishingPoly dom S) :
    ∀ i ∈ S ∩ A, R₀.eval (dom i) = (P - C γ * q).eval (dom i) := by
  intro i hi
  rw [Finset.mem_inter] at hi
  have hev := congrArg (Polynomial.eval (dom i)) hid
  rw [eval_mul, vanishingPoly_eval_eq_zero dom hi.1, mul_zero] at hev
  simp only [eval_sub, eval_add, eval_mul, eval_C] at hev ⊢
  rw [← hA i hi.2]
  linear_combination hev

/-- **Cross-frame witness separation inside `A`**: scalars carrying
distinct frames meet in fewer than `k` points of the agreement set. -/
theorem cross_frame_inter_le (hk : 1 ≤ k)
    {γ₁ γ₂ : F} {P₁ P₂ g₁ g₂ : F[X]} {A S₁ S₂ : Finset (Fin n)}
    (hA : ∀ i ∈ A, R₁.eval (dom i) = q.eval (dom i))
    (hfr : P₁ - C γ₁ * q ≠ P₂ - C γ₂ * q)
    (hd₁ : (P₁ - C γ₁ * q).natDegree < k)
    (hd₂ : (P₂ - C γ₂ * q).natDegree < k)
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂) :
    (S₁ ∩ S₂ ∩ A).card ≤ k - 1 := by
  classical
  have hroots : ∀ i ∈ S₁ ∩ S₂ ∩ A,
      ((P₁ - C γ₁ * q) - (P₂ - C γ₂ * q)).eval (dom i) = 0 := by
    intro i hi
    rw [Finset.mem_inter] at hi
    obtain ⟨hi12, hiA⟩ := hi
    rw [Finset.mem_inter] at hi12
    have h₁ := attached_R0_agrees_frame_on_A hA hid₁ i
      (Finset.mem_inter.mpr ⟨hi12.1, hiA⟩)
    have h₂ := attached_R0_agrees_frame_on_A hA hid₂ i
      (Finset.mem_inter.mpr ⟨hi12.2, hiA⟩)
    rw [eval_sub]
    rw [← h₁, ← h₂]
    ring
  have hWne : (P₁ - C γ₁ * q) - (P₂ - C γ₂ * q) ≠ 0 :=
    sub_ne_zero.mpr hfr
  have hdvd : vanishingPoly dom (S₁ ∩ S₂ ∩ A)
      ∣ (P₁ - C γ₁ * q) - (P₂ - C γ₂ * q) := by
    rw [vanishingPoly]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot]
      exact hroots i hi
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hWne
  rw [vanishingPoly_natDegree] at hdeg
  have hWdeg : ((P₁ - C γ₁ * q) - (P₂ - C γ₂ * q)).natDegree ≤ k - 1 := by
    have := natDegree_sub_le (P₁ - C γ₁ * q) (P₂ - C γ₂ * q)
    omega
  omega

/-- **The pencil-root cap**: a degree-`< k` pencil member vanishing on `k`
domain points degenerates — `R = C γ * Q` identically.  (The mechanism that
collapses every ladder escalation: deg ≤ 2 members have ≤ 2 roots.) -/
theorem pencil_degenerate_of_roots (hk : 1 ≤ k)
    {R Q : F[X]} {γ : F} {T : Finset (Fin n)}
    (hdR : R.natDegree < k) (hdQ : Q.natDegree < k) (hT : k ≤ T.card)
    (hvan : ∀ i ∈ T, R.eval (dom i) = γ * Q.eval (dom i)) :
    R = C γ * Q := by
  classical
  by_contra hne
  have hWne : R - C γ * Q ≠ 0 := sub_ne_zero.mpr hne
  have hdvd : vanishingPoly dom T ∣ R - C γ * Q := by
    rw [vanishingPoly]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot]
      have := hvan i hi
      simp only [IsRoot, eval_sub, eval_mul, eval_C]
      rw [this]
      ring
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hWne
  rw [vanishingPoly_natDegree] at hdeg
  have hCQ : (C γ * Q).natDegree < k :=
    lt_of_le_of_lt (natDegree_C_mul_le _ _) hdQ
  have hWdeg : (R - C γ * Q).natDegree < k := by
    have := natDegree_sub_le R (C γ * Q)
    omega
  omega

end FrameGeometry

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.attached_R0_agrees_frame_on_A
#print axioms ProximityGap.WBPencil.cross_frame_inter_le
#print axioms ProximityGap.WBPencil.pencil_degenerate_of_roots
