/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernel
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AffineCapture
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson

/-!
# K4 cell card bound from an *unconditional* affine-pinning family (#389, Johnson lane)

The in-tree `cell_card_le_of_decode_family_pinning` bounds a cell of bad scalars by `T` from a
*conditional* affine-pinning hypothesis (`T < Ecell.card → ∃ v₀ v₁, …`, "affine past threshold"),
routed through `claim1_dichotomy`.  This file supplies the *unconditional* downstream corollary: when
the decode family is pinned to a single affine pencil `(v₀, v₁)` on the **whole** cell, the cell has
at most `n = |D|` members — consuming the affine pair directly through the proven endgame count, no
threshold dichotomy.

* `affine_pair_from_decode_family_implies_improves` — the adapter: unconditional affine pinning of a
  `McaDecode` family forces every cell scalar `γ` to "improve" (the fold agreement makes the affine
  functional vanish at a coordinate of the factor disagreement set) — composing
  `McaDecode.affineCaptured` with `affineCaptured_improve`.
* `K4_cell_card_le_of_affine_pinning_family` — feeding that into the proven `factorImprove_card_le_n`
  (`|improving scalars| ≤ |disagreeSet| ≤ n`) gives `Ecell.card ≤ Fintype.card ι₀`.

This is the exact shape the K4 curve-capture consumers need; the deep content left is K4 itself
(supplying the unconditional affine pinning), which stays the named open obligation.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000


open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory Polynomial

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The adapter: unconditional affine pinning of a decode family forces every cell scalar to
improve.**  If every bad scalar `γ` of `Ecell` is decoded by some `McaDecode` whose polynomial is
`P γ`, and `P` is pinned to the affine pencil `P γ = v₀ + C γ · v₁` (degrees `< k`) on the whole
cell, then for every `γ ∈ Ecell` the fold agreement forces the affine functional to vanish at some
coordinate of the factor disagreement set — the `hImprove` shape the S8 endgame count consumes. -/
theorem affine_pair_from_decode_family_implies_improves
    {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0} {u : WordStack F₀ (Fin 2) ι₀}
    (Ecell : Finset F₀) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (v₀ v₁ : F₀[X]) (h₀ : v₀.natDegree < k) (h₁ : v₁.natDegree < k)
    (hpin : ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁) :
    ∀ γ ∈ Ecell, ∃ x ∈ disagreeSet (fun i => v₀.eval (domain i) - u 0 i)
        (fun i => v₁.eval (domain i) - u 1 i),
      affineGap (fun i => v₀.eval (domain i) - u 0 i)
        (fun i => v₁.eval (domain i) - u 1 i) γ x = 0 := by
  intro γ hγ
  obtain ⟨d, hd⟩ := hdec γ hγ
  exact affineCaptured_improve h₀ h₁ (d.affineCaptured (hd.trans (hpin γ hγ)))

/-- **K4 cell card bound from an unconditional affine pinning family.**  A cell whose bad scalars
are decoded by a family pinned to a single affine pencil `(v₀, v₁)` (degrees `< k`) has at most
`n = |D|` members: each scalar improves (the adapter), and the proven endgame count
`factorImprove_card_le_n` bounds the cell.  The *unconditional* downstream corollary of
`cell_card_le_of_decode_family_pinning`, consuming the affine pair directly. -/
theorem K4_cell_card_le_of_affine_pinning_family
    {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0} {u : WordStack F₀ (Fin 2) ι₀}
    (Ecell : Finset F₀) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (v₀ v₁ : F₀[X]) (h₀ : v₀.natDegree < k) (h₁ : v₁.natDegree < k)
    (hpin : ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁) :
    Ecell.card ≤ Fintype.card ι₀ :=
  factorImprove_card_le_n _ _ Ecell
    (affine_pair_from_decode_family_implies_improves Ecell P hdec v₀ v₁ h₀ h₁ hpin)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
