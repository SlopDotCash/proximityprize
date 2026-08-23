/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform pushforward under a balanced surjection

If `f : A → B` between finite types is surjective and all its fibers have equal cardinality, then
the uniform distribution on `A` pushes forward under `f` to the uniform distribution on `B`.

This is the clean abstraction behind the random-sampling uniform-marginal proofs in
`RandomLinearCodeEquidistribution.lean` (codeword map `G ↦ m ᵥ* G`) and the random-subset
inclusion marginals: each is an instance of a balanced surjection. Kernel-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace ArkLib.Probability

open scoped ENNReal

/-- **Uniform pushforward under a balanced surjection.** For a surjective `f : A → B` between
finite types all of whose fibers `{a | f a = b}` have the same cardinality, the uniform
distribution on `A` maps to the uniform distribution on `B`. -/
theorem map_uniformOfFintype_of_fiber_card_eq
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [DecidableEq B]
    (f : A → B) (hf : Function.Surjective f)
    (hfib : ∀ b₁ b₂ : B,
      (Finset.univ.filter (fun a => f a = b₁)).card
        = (Finset.univ.filter (fun a => f a = b₂)).card) :
    (PMF.uniformOfFintype A).map f = PMF.uniformOfFintype B := by
  classical
  ext b
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfilter :
      (Finset.univ.filter (fun a => b = f a)) = (Finset.univ.filter (fun a => f a = b)) := by
    apply Finset.filter_congr
    intro a _
    exact eq_comm
  rw [hfilter]
  set N : ℕ := (Finset.univ.filter (fun a => f a = b)).card with hN
  have hcardA : Fintype.card A = Fintype.card B * N := by
    have hpart := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset B))
      (fun a _ => Finset.mem_univ (f a))
    rw [Finset.card_univ] at hpart
    rw [hpart, Finset.sum_congr rfl (fun b' _ => hfib b' b), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  rw [hcardA]
  have hNne : (N : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < N := by
      rw [hN]
      apply Finset.card_pos.2
      obtain ⟨a, ha⟩ := hf b
      exact ⟨a, by simp [Finset.mem_filter, ha]⟩
    exact_mod_cast hpos.ne'
  have hBne : (Fintype.card B : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card B := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [Nat.cast_mul,
    ENNReal.mul_inv (Or.inl hBne) (Or.inl (ENNReal.natCast_ne_top (Fintype.card B))),
    ← mul_assoc, mul_comm (N : ℝ≥0∞) (Fintype.card B : ℝ≥0∞)⁻¹, mul_assoc,
    ENNReal.mul_inv_cancel hNne (ENNReal.natCast_ne_top N), mul_one]

end ArkLib.Probability

#print axioms ArkLib.Probability.map_uniformOfFintype_of_fiber_card_eq
