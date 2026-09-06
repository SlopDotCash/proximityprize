/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Coset invariance of the Gauss periods — tightening the tail union bound (#444)

The tail bridge `_AvW7` runs a union bound over all `q−1` nonzero frequencies. But the periods
`eta ψ G b = Σ_{y∈G} ψ(b·y)` are **invariant under multiplying `b` by any `g ∈ G`** when `G` is a
multiplicative subgroup (the substitution `y ↦ g·y` permutes `G`). Hence `b ↦ ‖eta ψ G b‖` is
constant on each coset `b·G`, there are only `(q−1)/|G|` distinct values, and the union bound's
effective index set shrinks from `q` to `q/|G|`. This replaces the threshold's `log q` with
`log(q/|G|)` — *exactly* the form of the project's live target
`GeneralizedPaleyNearRamanujan : ‖η_b‖² ≤ C·|G|·log(q/|G|)` (note the `q/|G|`, not `q`).

This file proves the structural invariance (the reusable fact). It is unconditional given the
subgroup-stability hypothesis `G` satisfies, and axiom-clean. (It tightens the *constant* in the
conditional chain; it does not touch the open tail hypothesis itself.) NOT prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW8

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Coset invariance of the period (proven).** If right-multiplication by `g` permutes `G`
(`(G.image (· * g)) = G`, the defining stability of a multiplicative subgroup under `g ∈ G`), then
`eta ψ G (g * b) = eta ψ G b`. Proof: reindex `Σ_{y∈G} ψ(g·b·y) = Σ_{y∈G} ψ(b·(g·y))` by the
bijection `y ↦ g·y` of `G`. -/
theorem eta_coset_invariant (ψ : AddChar F ℂ) (G : Finset F) (g b : F) (hg0 : g ≠ 0)
    (hg : G.image (fun y => g * y) = G) :
    eta ψ G (g * b) = eta ψ G b := by
  have hinj : ∀ a ∈ G, ∀ c ∈ G, g * a = g * c → a = c :=
    fun a _ c _ h => mul_left_cancel₀ hg0 h
  unfold eta
  -- reindex the RHS `Σ_{y∈G} ψ(b*y)` along the bijection `y ↦ g*y` of `G` (image = G):
  -- Σ_{y∈G} ψ(b*y) = Σ_{y∈G.image(g*·)} ψ(b*y) = Σ_{z∈G} ψ(b*(g*z)) = Σ_{z∈G} ψ((g*b)*z)
  conv_rhs => rw [← hg, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  ring

/-- **Constant on cosets (proven).** Under the same stability for every `g ∈ G`, the norm
`‖eta ψ G b‖` agrees across the coset: `‖eta ψ G (g*b)‖ = ‖eta ψ G b‖` for `g ∈ G`. So the tail
exceedance set `{b : T < ‖eta_b‖}` is a union of full `G`-cosets, and its cardinality is a multiple
of `|G|` — the union bound's effective range is `(q−1)/|G|` cosets, giving the `log(q/|G|)` threshold
that matches `GeneralizedPaleyNearRamanujan`. -/
theorem norm_eta_coset_invariant (ψ : AddChar F ℂ) (G : Finset F) (g b : F) (hg0 : g ≠ 0)
    (hg : G.image (fun y => g * y) = G) :
    ‖eta ψ G (g * b)‖ = ‖eta ψ G b‖ := by
  rw [eta_coset_invariant ψ G g b hg0 hg]

end ArkLib.ProximityGap.Frontier.AvW8

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW8.eta_coset_invariant
#print axioms ArkLib.ProximityGap.Frontier.AvW8.norm_eta_coset_invariant
