/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._AntipodalEvenOddDescent
import Mathlib.LinearAlgebra.Lagrange

/-!
# `IsolatedCountResidual` is false as stated

`IsolatedCountResidual F k` quantifies over every `E O : F[X]` with only `O.natDegree < k`;
`E` carries no degree bound and no subgroup, decodedness or support restriction. It asserts
that the isolated roots of `E(X²) - X·O(X²)` number at most `k + 1`.

At `k = 1` over `ℚ`, take `O = 1` and `E = -u²/6 + 7u/6`. Then `E(x²) = x` at
`x = 0, 1, 2` (`E(0)=0`, `E(1)=1`, `E(4)=2`), giving three isolated roots against the
claimed cap of `2`.

This refutes the recorded statement only. The intended restrictions (the halved-subgroup
domain and a degree bound on `E`) are not discharged here, and the underlying Kelley /
BGK general-position count remains open. It does not close #164.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ProximityGap.Frontier.IsolatedCountResidualRefuted

open AntipodalEvenOddDescent

/-- The interpolant `E(u) = -u²/6 + 7u/6`. -/
def E₀ : ℚ[X] := C (-1 / 6) * X ^ 2 + C (7 / 6) * X

/-- The three isolated roots `0, 1, 2` of `E₀(X²) - X · 1`. -/
theorem three_isolated_roots :
    (↑({0, 1, 2} : Finset ℚ) : Set ℚ) ⊆
      {x : ℚ | (E₀.comp (X ^ 2) - X * (C (1 : ℚ)).comp (X ^ 2)).IsRoot x ∧
        (C (1 : ℚ)).eval (x ^ 2) ≠ 0} := by
  intro x hx
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  refine ⟨?_, by simp⟩
  rcases hx with rfl | rfl | rfl <;> simp [E₀, IsRoot.def] <;> norm_num

/-- `IsolatedCountResidual ℚ 1` is false: three isolated roots exceed the cap `k + 1 = 2`. -/
theorem not_isolatedCountResidual_rat_one : ¬ IsolatedCountResidual ℚ 1 := by
  intro h
  have hc := (h E₀ (C 1) (by simp)).2 {0, 1, 2} three_isolated_roots
  have : ({0, 1, 2} : Finset ℚ).card = 3 := by decide +revert
  omega

/-! ## A family for every `k ≥ 1`, with `E` of degree at most `k + 1`

Interpolating `u ↦ √u` at the `k + 2` nodes `u_i = (i+1)²` gives `E` with
`E(u_i) = i + 1`. With `O = 1` every `x = i + 1` is an isolated root of `E(X²) - X`.
So `k + 2` isolated roots beat the cap `k + 1`, for every `k ≥ 1`. The degree of `E`
is below `k + 2`, so the failure is not caused by an
unbounded degree of `E`: `E(X²) - X·O(X²)` has degree below `2k + 4`. -/

/-- The interpolant of `(i+1)² ↦ i+1` on `i < k + 2`. -/
def Efam (k : ℕ) : ℚ[X] :=
  Lagrange.interpolate (Finset.range (k + 2)) (fun i : ℕ => ((i : ℚ) + 1) ^ 2)
    (fun i : ℕ => (i : ℚ) + 1)

theorem Efam_degree_lt (k : ℕ) : (Efam k).degree < ((k + 2 : ℕ) : WithBot ℕ) := by
  have := Lagrange.degree_interpolate_lt (s := Finset.range (k + 2))
    (v := fun i : ℕ => ((i : ℚ) + 1) ^ 2) (r := fun i : ℕ => (i : ℚ) + 1)
    (by
      intro a _ b _ hab
      have h1 : ((a : ℚ) + 1) ^ 2 = ((b : ℚ) + 1) ^ 2 := hab
      have h2 : ((a : ℚ) + 1) = ((b : ℚ) + 1) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
        · exact h
        · have : (0 : ℚ) ≤ a := Nat.cast_nonneg a
          have : (0 : ℚ) ≤ b := Nat.cast_nonneg b
          linarith
      exact_mod_cast (by linarith : (a : ℚ) = b))
  simpa [Efam] using this

theorem Efam_eval (k i : ℕ) (hi : i < k + 2) :
    (Efam k).eval (((i : ℚ) + 1) ^ 2) = (i : ℚ) + 1 := by
  unfold Efam
  exact Lagrange.eval_interpolate_at_node (s := Finset.range (k + 2))
    (v := fun i : ℕ => ((i : ℚ) + 1) ^ 2) (r := fun i : ℕ => (i : ℚ) + 1)
    (by
      intro a _ b _ hab
      have h1 : ((a : ℚ) + 1) ^ 2 = ((b : ℚ) + 1) ^ 2 := hab
      have h2 : ((a : ℚ) + 1) = ((b : ℚ) + 1) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
        · exact h
        · have : (0 : ℚ) ≤ a := Nat.cast_nonneg a
          have : (0 : ℚ) ≤ b := Nat.cast_nonneg b
          linarith
      exact_mod_cast (by linarith : (a : ℚ) = b))
    (Finset.mem_range.mpr hi)

/-- **Family.** For every `k ≥ 1`, `IsolatedCountResidual ℚ k` is false: the `k + 2` points
`1, …, k + 2` are isolated roots, against the cap `k + 1`. -/
theorem not_isolatedCountResidual_rat (k : ℕ) (hk : 1 ≤ k) :
    ¬ IsolatedCountResidual ℚ k := by
  intro h
  have hsub : (↑((Finset.range (k + 2)).image (fun i : ℕ => (i : ℚ) + 1)) : Set ℚ) ⊆
      {x : ℚ | ((Efam k).comp (X ^ 2) - X * (C (1 : ℚ)).comp (X ^ 2)).IsRoot x ∧
        (C (1 : ℚ)).eval (x ^ 2) ≠ 0} := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨?_, by simp⟩
    simp [IsRoot.def, Efam_eval k i hi]
  have hc := (h (Efam k) (C 1) (by simpa using hk)).2 _ hsub
  have hcard : ((Finset.range (k + 2)).image (fun i : ℕ => (i : ℚ) + 1)).card = k + 2 := by
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      have : (a : ℚ) = b := by simpa using hab
      exact_mod_cast this)]
    simp
  omega

end ProximityGap.Frontier.IsolatedCountResidualRefuted

#print axioms ProximityGap.Frontier.IsolatedCountResidualRefuted.three_isolated_roots
#print axioms ProximityGap.Frontier.IsolatedCountResidualRefuted.not_isolatedCountResidual_rat_one
#print axioms ProximityGap.Frontier.IsolatedCountResidualRefuted.Efam_eval
#print axioms ProximityGap.Frontier.IsolatedCountResidualRefuted.Efam_degree_lt
#print axioms ProximityGap.Frontier.IsolatedCountResidualRefuted.not_isolatedCountResidual_rat
