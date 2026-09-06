/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

/-!
# Bridge B39 — `ε_mca ≥ incidence/q` as a packaged bridge lemma (#444)

This file CONSUMES the in-tree far-coset explosion fact
`FarCosetExplosion.epsMCA_ge_far_incidence` and repackages it as a single
named bridge lemma in the open-core vocabulary used by the #444 programme:

> the MCA error at radius `δ` is bounded below by the **line-explainability
> incidence** of the affine line `u₀ + γ·u₁` (far direction `u₁`) against the
> witness-sized agreement ball, divided by the field size `q`.

No new mathematics is introduced: this is a faithful restatement / API surface
for downstream consumers (the line–ball incidence attack face, face 4 of the
open core). The incidence count is given a name (`lineIncidenceCount`) so the
bound reads `ε_mca(C,δ) ≥ lineIncidenceCount / q`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.BridgeB39

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The line-explainability incidence count.**  The number of scalars `γ` for
which the affine line `u₀ + γ·u₁` agrees with some codeword of `C` on a
witness-sized set (`≥ (1−δ)·n` coordinates).  This is the binding combinatorial
object of the explosion regime (face 4 of the open core). -/
noncomputable def lineIncidenceCount (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ :=
  (Finset.univ.filter (fun γ : F =>
    ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card

open Classical in
/-- **Bridge B39 — `ε_mca ≥ incidence / q`.**  For any far direction `u₁` and
offset `u₀`, the MCA error of `C` at radius `δ` is at least the line-explainability
incidence divided by the field size:

  `ε_mca(C, δ) ≥ lineIncidenceCount(C, δ, u₀, u₁) / q`.

This is a packaged restatement of `FarCosetExplosion.epsMCA_ge_far_incidence`
in the named-count vocabulary. Pinning `δ*` from below is exactly bounding the
maximum such incidence; pinning from above is constructing a high-incidence
far line. -/
theorem epsMCA_ge_incidence_over_q (C : Set (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (hfar : FarCosetExplosion.FarFromCode C δ u₁) :
    (lineIncidenceCount (F := F) C δ u₀ u₁ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := A) C δ := by
  simpa only [lineIncidenceCount] using
    FarCosetExplosion.epsMCA_ge_far_incidence (F := F) (A := A) C δ
      (u₀ := u₀) (u₁ := u₁) hfar

end ProximityGap.BridgeB39

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BridgeB39.epsMCA_ge_incidence_over_q
