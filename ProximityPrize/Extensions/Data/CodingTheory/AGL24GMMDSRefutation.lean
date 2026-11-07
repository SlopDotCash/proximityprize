/-
Copyright (c) 2026 Adolius. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Adolius
-/
import ArkLib.Data.CodingTheory.AGL24GrandAssembly

/-! # Small-field obstruction to the unrestricted GM-MDS interface -/

open AGL24

/-- The unconditional GM-MDS interface residual is false when the ambient field size
is strictly smaller than the edge index set (`|F| < |ι|`).

The classical GM-MDS theorem (Lovett 2018 / [AGL24] Theorem A.2) requires an evaluation
embedding `φ : ι ↪ F` (which requires `|ι| ≤ |F|`, typically `|F| > n`). Stated as an
unconstrained residual over arbitrary finite fields `F` and index types `ι`, it fails
for small fields (e.g., `ι = Fin 3`, `F = ZMod 2`) because `GZPCondition` holds vacuously
for the zero multiplicity function `δ = 0`, but no injection `Fin 3 ↪ ZMod 2` exists
by the pigeonhole principle. -/
theorem not_gmmdsResidual_fin3_zmod2 (k : ℕ) :
    ¬ GMMDSResidual (Fin 3) (ZMod 2) k := by
  intro h
  have hgzp : GZPCondition (ι := Fin 3) (V := Fin 2)
      (fun _ => (∅ : Finset (Fin 2))) (fun _ => 0) k := by
    intro κ hκ hpos
    have hzero : ∀ j : Fin 2, κ j = 0 := by
      intro j
      have hj : κ j ≤ 0 := hκ j
      omega
    have hsum : ∑ j : Fin 2, κ j = 0 := by simp [hzero]
    omega
  obtain ⟨φ, _, _, _, _⟩ := h (fun _ => ∅) (fun _ => 0) hgzp
  have hle := Fintype.card_le_of_injective φ φ.injective
  revert hle
  decide

#print axioms not_gmmdsResidual_fin3_zmod2
