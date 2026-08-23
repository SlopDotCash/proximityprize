/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADualPencilLaw

/-!
# Circuit collision propagation (#357 round 10): how the matroid limits the census

The wide circuits of the dual-vector matroid (classified by the pencil criterion) limit
the sub-threshold collision census through one mechanism, proven here:

* `pairing_combo` — a vector dependency `α·λ¹ + β·λ² + γ·λ³ = 0` pairs against any word
  to an affine relation among the syndromes `⟨λ^X, u⟩`.
* **`circuit_collision_propagation`** — on a wide circuit, **collisions propagate**: if
  two of the three witness sets carry the *same* interpolation scalar
  (`⟨λ^X, u₀⟩ = −g·⟨λ^X, u₁⟩`), then the third carries it too (whenever its
  `b`-syndrome is nonzero). Equivalently: **no stack can realize a 2–1 split of scalars
  on a circuit** — the scalar pattern of every circuit is all-equal or all-distinct.

This is the exact census-limiting law: the maximum number of distinct interpolation
scalars a stack can realize (= the bad-scalar census at sub-threshold `q`, by the
syndrome representation of `γ_S`) is the maximum size of a "rainbow-or-monochrome"
labelling of the witness layer constrained by the circuit list — a purely combinatorial
optimization over the (now fully stratified) circuit hypergraph. With the horizontal and
vertical strata closed and the parabola negative law, the production-scale census
question is this optimization over the classified circuits.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (rounds 6–10); `MCADualPencilLaw.lean`, `MCAIncidenceCensus.lean`,
  `MCAVerticalStratumCharZero.lean`, `MCAParabolaStratification.lean`.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace ProximityGap.MCACircuitPropagation

open ProximityGap.MCADualPencilLaw

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The syndrome pairing of a dual vector against a word. -/
noncomputable def pairing (lam u : ι → F) : F := ∑ i, lam i * u i

/-- A pointwise vector dependency pairs to an affine relation among syndromes. -/
theorem pairing_combo {l₁ l₂ l₃ : ι → F} {α β γ : F}
    (hdep : ∀ i, α * l₁ i + β * l₂ i + γ * l₃ i = 0) (u : ι → F) :
    α * pairing l₁ u + β * pairing l₂ u + γ * pairing l₃ u = 0 := by
  unfold pairing
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
  apply Finset.sum_congr rfl
  intro i _
  have h := hdep i
  linear_combination u i * h

/-- **The circuit collision-propagation law.** On a wide circuit
(`α·λ¹ + β·λ² + γ·λ³ = 0`, `γ ≠ 0`): if witness sets `1` and `2` both carry the
interpolation scalar `g` (syndrome form `a_X = −g·b_X`), then so does witness set `3`,
provided its `b`-syndrome is nonzero. No stack realizes a 2–1 scalar split on a
circuit. -/
theorem circuit_collision_propagation {l₁ l₂ l₃ : ι → F} {α β γ : F} (hγ : γ ≠ 0)
    (hdep : ∀ i, α * l₁ i + β * l₂ i + γ * l₃ i = 0) (u₀ u₁ : ι → F) {g : F}
    (h1 : pairing l₁ u₀ = -g * pairing l₁ u₁)
    (h2 : pairing l₂ u₀ = -g * pairing l₂ u₁) :
    pairing l₃ u₀ = -g * pairing l₃ u₁ := by
  have ha := pairing_combo hdep u₀
  have hb := pairing_combo hdep u₁
  have hkey : γ * (pairing l₃ u₀ + g * pairing l₃ u₁) = 0 := by
    linear_combination ha + g * hb - α * h1 - β * h2
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hγ
  · linear_combination h

/-- **The 2–1 split impossibility (census form).** On a wide circuit with all three
coefficients nonzero and all three `b`-syndromes nonzero, the three interpolation
scalars `γ_X = −a_X/b_X` cannot take a pattern with exactly two equal: equal on any two
implies equal on all three. -/
theorem no_two_one_split {l₁ l₂ l₃ : ι → F} {α β γ : F}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hdep : ∀ i, α * l₁ i + β * l₂ i + γ * l₃ i = 0) (u₀ u₁ : ι → F)
    (hb1 : pairing l₁ u₁ ≠ 0) (hb2 : pairing l₂ u₁ ≠ 0) (hb3 : pairing l₃ u₁ ≠ 0) :
    ∀ g : F,
      ((pairing l₁ u₀ = -g * pairing l₁ u₁ ∧ pairing l₂ u₀ = -g * pairing l₂ u₁) →
        pairing l₃ u₀ = -g * pairing l₃ u₁) ∧
      ((pairing l₁ u₀ = -g * pairing l₁ u₁ ∧ pairing l₃ u₀ = -g * pairing l₃ u₁) →
        pairing l₂ u₀ = -g * pairing l₂ u₁) ∧
      ((pairing l₂ u₀ = -g * pairing l₂ u₁ ∧ pairing l₃ u₀ = -g * pairing l₃ u₁) →
        pairing l₁ u₀ = -g * pairing l₁ u₁) := by
  intro g
  refine ⟨fun ⟨h1, h2⟩ => circuit_collision_propagation hγ hdep u₀ u₁ h1 h2,
    fun ⟨h1, h3⟩ => ?_, fun ⟨h2, h3⟩ => ?_⟩
  · -- permute the dependency to expose l₂
    have hdep' : ∀ i, α * l₁ i + γ * l₃ i + β * l₂ i = 0 := by
      intro i
      linear_combination hdep i
    exact circuit_collision_propagation hβ hdep' u₀ u₁ h1 h3
  · have hdep' : ∀ i, β * l₂ i + γ * l₃ i + α * l₁ i = 0 := by
      intro i
      linear_combination hdep i
    exact circuit_collision_propagation hα hdep' u₀ u₁ h2 h3

/-! ## Source audit -/

#print axioms pairing_combo
#print axioms circuit_collision_propagation
#print axioms no_two_one_split

end ProximityGap.MCACircuitPropagation
