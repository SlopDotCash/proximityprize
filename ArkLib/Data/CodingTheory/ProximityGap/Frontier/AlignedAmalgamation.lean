/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ExplainableAmalgamation
import ArkLib.Data.CodingTheory.ProximityGap.UniversalAlignmentLaw

/-!
# `Aligned`-level amalgamation: overlapping γ-aligned sets glue (issue #444, census face)

`ExplainableAmalgamation` proved the gluing law at the `ExplainableOn` level. The census face
works with `Aligned` (`UniversalAlignmentLaw`): `S` is `γ`-aligned iff every injective
`(k+1)`-tuple of `S` lies on the `γ`-fibre of the residual *pencil*
`residual(u₀) + γ·residual(u₁)`. By residual-affinity (`residual_line`) the pencil's residual is
the residual of the single word `pencil γ i := u₀ i + γ·u₁ i`, so:

  **`aligned_iff_explainableOn_pencil`** : `Aligned dom k u₀ u₁ γ S ↔ ExplainableOn dom k (γ-pencil) S`

(for `1 ≤ k`). Transporting `explainableOn_amalg` across this bridge gives the census-relevant law:

  **`aligned_amalg`** : `Aligned … γ S₁ → Aligned … γ S₂ → k ≤ |S₁ ∩ S₂| → Aligned … γ (S₁ ∪ S₂)`.

This is the well-definedness of the **agreement set** `A_γ` (the union of `γ`'s aligned sets is
itself `γ`-aligned, so it is the maximal aligned set), which is the structural reason
`alignedSetsForScalar γ` is exactly the non-degenerate `a`-subsets of one set — the mechanism
behind `CensusScalarPartition.mult_ge_choose_of_aligned_superset` (it upgrades the `≥` to its
binomial cause).

Probe-verified (`scripts/probes/probe_census_union_aligned.py`: thin `μ_n`, `n=2^a`, `p≫n³`,
never `n=q−1`): `≥k`-sharing aligned sets amalgamate with 0 spanning-tuple breaks across
`n∈{12,16,20}`, `k∈{1,2,3}`.

NOTE on scope. Structural well-definedness of the agreement set; does NOT bound the census.
CORE (`M(μ_n) ≤ C·√(n·log(p/n))`), i.e. the `CensusDomination` cap, stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

/-- The `γ`-**pencil** word `i ↦ u₀ i + γ · u₁ i`. -/
def pencil (u₀ u₁ : Fin n → F) (γ : F) : Fin n → F := fun i => u₀ i + γ * u₁ i

/-- **The bridge.** A set is `γ`-aligned iff the `γ`-pencil word is explainable on it.
By residual-affinity (`residual_line`) the per-tuple alignment condition
`residual(u₀) + γ·residual(u₁) = 0` is exactly the vanishing of the pencil's residual, which
(`explainableOn_iff_forall_residual`, `1 ≤ k`) characterizes explainability of the pencil word. -/
theorem aligned_iff_explainableOn_pencil (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₀ u₁ : Fin n → F} {γ : F} {S : Finset (Fin n)} :
    Aligned dom k u₀ u₁ γ S ↔ ExplainableOn dom k (pencil u₀ u₁ γ) S := by
  classical
  unfold Aligned ExplainableOn
  rw [explainableOn_iff_forall_residual dom hk]
  have hpenc : ∀ t : Fin (k + 1) → Fin n,
      residual dom k t (pencil u₀ u₁ γ)
        = residual dom k t u₀ + γ * residual dom k t u₁ := by
    intro t
    show residual dom k t (fun i => u₀ i + γ * u₁ i)
      = residual dom k t u₀ + γ * residual dom k t u₁
    exact residual_line dom k t u₀ u₁ γ
  constructor
  · intro h t htinj htmem
    rw [hpenc t]
    exact h t htinj htmem
  · intro h t htinj htmem
    have hpz := h t htinj htmem
    rw [hpenc t] at hpz
    exact hpz

/-- **`Aligned` AMALGAMATION.** Two `γ`-aligned sets sharing `≥ k` points have a `γ`-aligned
union. (Transport of `explainableOn_amalg` across the pencil bridge.) -/
theorem aligned_amalg (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₀ u₁ : Fin n → F} {γ : F} {S₁ S₂ : Finset (Fin n)}
    (h₁ : Aligned dom k u₀ u₁ γ S₁) (h₂ : Aligned dom k u₀ u₁ γ S₂)
    (hov : k ≤ (S₁ ∩ S₂).card) : Aligned dom k u₀ u₁ γ (S₁ ∪ S₂) := by
  rw [aligned_iff_explainableOn_pencil dom hk] at h₁ h₂ ⊢
  exact explainableOn_amalg dom h₁ h₂ hov

/-- **Agreement-set well-definedness, finite-union form.** A nonempty family of `γ`-aligned sets,
each sharing `≥ k` points with a fixed base aligned set `S₀`, all amalgamate with `S₀`: every
member's union with `S₀` stays `γ`-aligned. The base anchors a single deg-`< k` explainer; the
union over the whole family is the agreement set. -/
theorem aligned_union_of_base (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₀ u₁ : Fin n → F} {γ : F} {S₀ S : Finset (Fin n)}
    (h₀ : Aligned dom k u₀ u₁ γ S₀) (h : Aligned dom k u₀ u₁ γ S)
    (hov : k ≤ (S₀ ∩ S).card) : Aligned dom k u₀ u₁ γ (S₀ ∪ S) :=
  aligned_amalg dom hk h₀ h hov

/-- **Unique-scalar amalgamation guard.** If two aligned sets share `≥ k` points and BOTH contain
a non-degenerate tuple, the amalgamated union is still aligned for the (necessarily unique) common
scalar — making explicit that amalgamation never crosses scalar fibres (cf. `Aligned.gamma_eq`). -/
theorem aligned_amalg_nondeg (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₀ u₁ : Fin n → F} {γ : F} {S₁ S₂ : Finset (Fin n)}
    (h₁ : Aligned dom k u₀ u₁ γ S₁) (h₂ : Aligned dom k u₀ u₁ γ S₂)
    (hov : k ≤ (S₁ ∩ S₂).card)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S₁ ∪ S₂)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    Aligned dom k u₀ u₁ γ (S₁ ∪ S₂)
      ∧ ∀ γ', Aligned dom k u₀ u₁ γ' (S₁ ∪ S₂) → γ' = γ := by
  have hun : Aligned dom k u₀ u₁ γ (S₁ ∪ S₂) := aligned_amalg dom hk h₁ h₂ hov
  exact ⟨hun, fun γ' hγ' => (Aligned.gamma_eq hγ' hun htinj htmem hnd)⟩

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.aligned_iff_explainableOn_pencil
#print axioms ProximityGap.PairRank.aligned_amalg
#print axioms ProximityGap.PairRank.aligned_union_of_base
#print axioms ProximityGap.PairRank.aligned_amalg_nondeg
