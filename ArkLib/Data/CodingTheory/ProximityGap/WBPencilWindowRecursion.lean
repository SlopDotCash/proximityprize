/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilRationalReduction

/-!
# The window recursion step (#371): rational-pair badness IS multiplier-GRS proximity

The formal interface for the window residual.  For a genuinely rational stack
(`u_j = R_j/ℓ_j`, denominators nonvanishing on the domain), a scalar's
line-explainability at slack `w` is EQUIVALENT to a proximity statement one level
deeper:

  `u₀ + γ·u₁` explainable  ⟺  the cleared pencil `ℓ₁·R₀ + γ·ℓ₀·R₁` agrees with
  some `P·ℓ₀·ℓ₁` (`deg P < k`) on `≥ n − w` domain points.

The right side is proximity of a γ-line to the **multiplier code**
`{(P·ℓ₀ℓ₁)(xᵢ)} = GRS_k` with weights `ℓ₀ℓ₁(xᵢ) ≠ 0` — the same shape of problem
with parameters `(w, k) → (w, k)` at the cleared level but degree budget
`2w + k − 1` for the pencil: the recursion that degrades to `(3w, 2w+k)` when
iterated naively (the documented wall), and which the Möbius-descent attack
shortcuts on the σ-invariant family.  This file pins the step exactly, so the
window Prop `WindowRationalBounded` can be consumed and attacked in its
multiplier-GRS form.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The window recursion step, forward**: explainability of the rational line
clears to pencil–multiplier agreement on the same witness. -/
theorem cleared_agreement_of_explainable (dom : Fin n ↪ F) {k w : ℕ}
    {ℓ₀ ℓ₁ R₀ R₁ : F[X]}
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0) {γ : F}
    (h : ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ S, c i = R₀.eval (dom i) / ℓ₀.eval (dom i)
          + γ * (R₁.eval (dom i) / ℓ₁.eval (dom i))) :
    ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ P : F[X], P.degree < k ∧ ∀ i ∈ S,
        (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)).eval (dom i)
          = (P * (ℓ₀ * ℓ₁)).eval (dom i) := by
  obtain ⟨S, hS, c, hc, hag⟩ := h
  obtain ⟨P, hPdeg, rfl⟩ := hc
  refine ⟨S, hS, P, hPdeg, fun i hi => ?_⟩
  have h := hag i hi
  have h0 := hℓ₀v i
  have h1 := hℓ₁v i
  have hP : P.eval (dom i) = R₀.eval (dom i) / ℓ₀.eval (dom i)
      + γ * (R₁.eval (dom i) / ℓ₁.eval (dom i)) := h
  simp only [eval_add, eval_mul, eval_C]
  rw [hP]
  field_simp

/-- **The window recursion step, backward**: pencil–multiplier agreement divides
back to explainability of the rational line on the same witness. -/
theorem explainable_of_cleared_agreement (dom : Fin n ↪ F) {k w : ℕ}
    {ℓ₀ ℓ₁ R₀ R₁ : F[X]}
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0) {γ : F}
    (h : ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ P : F[X], P.degree < k ∧ ∀ i ∈ S,
        (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)).eval (dom i)
          = (P * (ℓ₀ * ℓ₁)).eval (dom i)) :
    ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ S, c i = R₀.eval (dom i) / ℓ₀.eval (dom i)
          + γ * (R₁.eval (dom i) / ℓ₁.eval (dom i)) := by
  obtain ⟨S, hS, P, hPdeg, hag⟩ := h
  refine ⟨S, hS, fun i => P.eval (dom i), ⟨P, hPdeg, rfl⟩, fun i hi => ?_⟩
  have h := hag i hi
  have h0 := hℓ₀v i
  have h1 := hℓ₁v i
  simp only [eval_add, eval_mul, eval_C] at h
  show P.eval (dom i) = R₀.eval (dom i) / ℓ₀.eval (dom i)
    + γ * (R₁.eval (dom i) / ℓ₁.eval (dom i))
  field_simp
  linear_combination -h

/-- **The window recursion equivalence**: for genuinely rational stacks,
line-explainability at slack `w` IS proximity of the cleared pencil to the
multiplier-GRS code — the formal one-level-deeper form of the window residual. -/
theorem explainable_iff_cleared (dom : Fin n ↪ F) {k w : ℕ}
    {ℓ₀ ℓ₁ R₀ R₁ : F[X]}
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0) (γ : F) :
    (∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ S, c i = R₀.eval (dom i) / ℓ₀.eval (dom i)
          + γ * (R₁.eval (dom i) / ℓ₁.eval (dom i)))
    ↔ (∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ P : F[X], P.degree < k ∧ ∀ i ∈ S,
        (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)).eval (dom i)
          = (P * (ℓ₀ * ℓ₁)).eval (dom i)) :=
  ⟨cleared_agreement_of_explainable dom hℓ₀v hℓ₁v,
    explainable_of_cleared_agreement dom hℓ₀v hℓ₁v⟩

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.cleared_agreement_of_explainable
#print axioms ProximityGap.WBPencil.explainable_of_cleared_agreement
#print axioms ProximityGap.WBPencil.explainable_iff_cleared
