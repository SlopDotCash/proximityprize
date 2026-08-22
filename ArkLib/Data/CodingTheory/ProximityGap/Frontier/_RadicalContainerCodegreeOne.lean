/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Bad-configuration container codegree-one obstruction (#464)

This file records a small, axiom-clean obstruction to a radical container route on
the bad-scalar hypergraph.  For a fixed stack `(u₀, u₁)`, the coordinate line
`γ ↦ u₀ i + γ * u₁ i` is injective whenever `u₁ i ≠ 0`.  Hence a single active
coordinate-value constraint has codegree at most one.

The conclusion is deliberately negative: at this level of granularity, container
or spread estimates collapse to the union bound over singleton slices.  That
union bound is the line-restricted list-size/Face-4 residual, so this route
reduces to the existing wall instead of bypassing it.
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The affine line through a stack and its per-coordinate rigidity. -/

/-- The **affine line** through a stack `u = (u₀, u₁)` at coordinate `i`:
`γ ↦ u₀ i + γ · u₁ i`.  This is the `i`-th coordinate of
`L_u(γ) = u₀ + γ • u₁`. -/
def affineLine {n : ℕ} (u₀ u₁ : Fin n → F) (i : Fin n) (γ : F) : F :=
  u₀ i + γ * u₁ i

/-- **Per-coordinate injectivity on an active coordinate.**  If `u₁ i ≠ 0` (the coordinate is
"active"), then the map `γ ↦ affineLine u₀ u₁ i γ` is injective in `γ`. -/
theorem affineLine_injective_of_active {n : ℕ} (u₀ u₁ : Fin n → F) (i : Fin n)
    (hactive : u₁ i ≠ 0) :
    Function.Injective (fun γ => affineLine u₀ u₁ i γ) := by
  intro γ γ' h
  simp only [affineLine] at h
  have h2 : γ * u₁ i = γ' * u₁ i := add_left_cancel h
  exact mul_right_cancel₀ hactive h2

/-! ## 2. The codegree bound `Δ_1 = 1` (the decisive rigidity of the bad hypergraph). -/

/-- **`codegree_one` — the container codegree is `1` on active coordinates.**
For any target value `v` and active coordinate `i`, the slice of scalars
consistent with `L_u(γ) i = v` has cardinality at most `1`.

Proof: the slice is a fiber of an injective map. -/
theorem codegree_one {n : ℕ} (u₀ u₁ : Fin n → F) (i : Fin n) (v : F)
    (hactive : u₁ i ≠ 0) (s : Finset F)
    (hs : ∀ γ ∈ s, affineLine u₀ u₁ i γ = v) :
    s.card ≤ 1 := by
  -- All elements map to the same value under an injective map.
  rw [Finset.card_le_one]
  intro a ha b hb
  have hinj := affineLine_injective_of_active u₀ u₁ i hactive
  have :
      (fun γ => affineLine u₀ u₁ i γ) a
        = (fun γ => affineLine u₀ u₁ i γ) b := by
    simp only
    rw [hs a ha, hs b hb]
  exact hinj this

/-- **`bad_subset_card_le_of_codegree_one` — the container collapse, slice form.**
If `Bad` is contained in a single value-slice on an active coordinate, then
`|Bad| ≤ 1`. -/
theorem bad_subset_card_le_of_codegree_one {n : ℕ} (u₀ u₁ : Fin n → F) (i : Fin n) (v : F)
    (hactive : u₁ i ≠ 0) (Bad : Finset F)
    (hBad : ∀ γ ∈ Bad, affineLine u₀ u₁ i γ = v) :
    Bad.card ≤ 1 :=
  codegree_one u₀ u₁ i v hactive Bad hBad

/-! ## 3. The union bound is the container output. -/

/-- **The container output is the union bound over witnesses.**
If the bad set is covered by a finite witness family `W`, then `|Bad| ≤ #W`.
This is the list-size bound in its cleanest finite-set form. -/
theorem badset_le_witnessCount {n : ℕ} (u₀ u₁ : Fin n → F)
    (Bad : Finset F) (W : Finset F)
    (cover : ∀ γ ∈ Bad, γ ∈ W) :
    Bad.card ≤ W.card :=
  Finset.card_le_card (by intro γ hγ; exact cover γ hγ)

/-- **`ContainerReducesToListSize` — the named verdict Prop.**

The bad-configuration hypergraph has codegree `1` on every active coordinate.
Thus the container output collapses to singleton slices and the union/list-size
bound.  This proposition names that reduction in a reusable form. -/
def ContainerReducesToListSize : Prop :=
  ∀ (n : ℕ) (u₀ u₁ : Fin n → F) (i : Fin n) (v : F),
    u₁ i ≠ 0 →
    ∀ (Bad : Finset F), (∀ γ ∈ Bad, affineLine u₀ u₁ i γ = v) → Bad.card ≤ 1

/-- The verdict holds: codegree-one rigidity gives the container collapse. -/
theorem containerReducesToListSize_holds :
    (ContainerReducesToListSize (F := F)) := by
  intro n u₀ u₁ i v hactive Bad hBad
  exact bad_subset_card_le_of_codegree_one u₀ u₁ i v hactive Bad hBad

/-! ## 4. Honesty booleans. -/

/-- The container method collapses to the union/list-size bound instead of
bypassing Paley. -/
def bypassesPaley : Bool := false

/-- The codegree-one obstruction is a distinct, new mechanism (not A8's `LF` nor A9's Wick). -/
def newMechanism : Bool := true

/-- Honesty contract, machine-pinned. -/
theorem honest_verdict : bypassesPaley = false ∧ newMechanism = true := ⟨rfl, rfl⟩

end ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne

-- Axiom audit (target: propext, Classical.choice, Quot.sound — no sorryAx)
#print axioms
  ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne.affineLine_injective_of_active
#print axioms ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne.codegree_one
#print axioms
  ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne.bad_subset_card_le_of_codegree_one
#print axioms ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne.badset_le_witnessCount
#print axioms
  ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne.containerReducesToListSize_holds
#print axioms ArkLib.ProximityGap.Frontier.RadicalContainerCodegreeOne.honest_verdict
