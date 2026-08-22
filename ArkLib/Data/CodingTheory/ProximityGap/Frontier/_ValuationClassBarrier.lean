/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# The valuation-class barrier (Sense-B irreducibility for the proximity prize, #444)

The proximity-prize floor reduces (two-sided, in-tree) to the archimedean sup-norm
`M(n) = max_{b≢0} |Σ_{x∈μ_n} e_p(b x)|`, which via the Gauss-sum / additive-energy decomposition is
governed by the archimedean absolute values `w α` (over the infinite places `w`) of cyclotomic algebraic
integers `α ∈ 𝓞 K`, `K = ℚ(ζ_n)`.

Every "p-adic / cohomological / Stickelberger / crystalline-valuation" input of a proof depends only on the
**ideal** `(α)` — equivalently, it is invariant under multiplying `α` by a unit `u ∈ (𝓞 K)ˣ`.  This file
formalizes the rigorous core of the Sense-B barrier:

> **Valuation/ideal data does not determine the archimedean profile.**

Concretely, whenever there is a non-torsion unit (i.e. the unit rank is positive — Dirichlet), there is an
infinite place `w` with `w u ≠ 1`, so the associates `α` and `u·α` share the ideal `(α)` yet differ in
archimedean absolute value at `w`.  Hence no unit-invariant functional (the entire valuation column) can pin
`w ↦ w α`, in particular cannot bound its supremum `M(n)`.  This is a *method-class barrier* (it bounds what
valuation-class proofs can do); it is **not** an undecidability claim and does **not** by itself prove the
floor.  See `docs/kb/Iinf-campaign/28-irreducibility-theorem-rigorous.md`.

## Main results
* `exists_infinitePlace_ne_one` — a non-torsion unit acts non-trivially on the archimedean profile.
* `profile_not_ideal_invariant` — `α` and `u·α` (same ideal) differ at some infinite place.
* `valuationClass_barrier` — the barrier: a non-torsion unit (exists iff unit rank `> 0`, Dirichlet)
  witnesses that valuation-class (unit-invariant) input cannot determine the archimedean profile.
-/

open NumberField NumberField.Units NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem

namespace ArkLib.ProximityGap.ValuationClassBarrier

variable {K : Type*} [Field K] [NumberField K]

/-- **Non-torsion units act non-trivially on the archimedean profile.**
Any unit `u` that is not a root of unity has some infinite place `w` with `w u ≠ 1`.  (If every infinite
place had `w u = 1` then the logarithmic embedding of `u` would vanish, forcing `u` into the torsion
subgroup by `logEmbedding_eq_zero_iff`.) -/
theorem exists_infinitePlace_ne_one {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    ∃ w : InfinitePlace K, w (u : K) ≠ 1 := by
  by_contra h
  push_neg at h
  apply hu
  rw [← logEmbedding_eq_zero_iff]
  ext w
  simp only [logEmbedding_component, h w.val, Real.log_one, mul_zero, Pi.zero_apply]

/-- **The archimedean profile is not ideal-invariant.**
For `α ≠ 0` and a non-torsion unit `u`, the associates `α` and `u·α` generate the same ideal `(α)` but have
different archimedean absolute values at some infinite place `w`.  Therefore no unit-invariant (ideal /
valuation) functional determines the profile `w ↦ w α`, in particular not its supremum. -/
theorem profile_not_ideal_invariant {u : (𝓞 K)ˣ} (hu : u ∉ torsion K)
    {α : K} (hα : α ≠ 0) : ∃ w : InfinitePlace K, w ((u : K) * α) ≠ w α := by
  obtain ⟨w, hw⟩ := exists_infinitePlace_ne_one (K := K) hu
  refine ⟨w, fun heq => hw ?_⟩
  rw [map_mul] at heq
  have hwα : w α ≠ 0 := (pos_iff.mpr hα).ne'
  have hmul : w (u : K) * w α = 1 * w α := by rw [one_mul]; exact heq
  exact mul_right_cancel₀ hwα hmul

/-- **The valuation-class barrier.**
Given any non-torsion unit `u` (such a unit exists exactly when the unit rank is positive — Dirichlet's
unit theorem, e.g. `NumberField.Units.fundSystem`), for every `α ≠ 0` the associates `α` and `u·α` share the
ideal `(α)` but differ in archimedean absolute value at some infinite place.  Hence no proof whose
field-arithmetic input is unit-invariant — i.e. a functional of the ideal `(α)` / the valuations
`(v_𝔭 α)`: the entire cohomological / Stickelberger / crystalline-valuation column — can determine the
archimedean profile `w ↦ w α`, and in particular cannot bound its supremum `M(n)`.

This is a *method-class* barrier (Sense-B irreducibility): it bounds what the valuation column of a
proof can achieve.  It is **not** an undecidability statement, and it does not cover phase-aware
p-adic input (the Gross–Koblitz `Γ_p`-unit is finer than the valuation). -/
theorem valuationClass_barrier {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) {α : K} (hα : α ≠ 0) :
    ∃ w : InfinitePlace K, w ((u : K) * α) ≠ w α :=
  profile_not_ideal_invariant (K := K) hu hα

end ArkLib.ProximityGap.ValuationClassBarrier

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.ValuationClassBarrier.exists_infinitePlace_ne_one
#print axioms ArkLib.ProximityGap.ValuationClassBarrier.valuationClass_barrier
