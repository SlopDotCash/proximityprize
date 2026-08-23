/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALYMCeiling

/-!
# Full-layer supply and the exact staircase (#357 round 4)

The window-interior cells pinned so far all follow one pattern: a stack whose bad scalars
biject with the **full layer** of `C(n,t)` witness sets meets the LYM ceiling. This file
names that pattern and proves the conditional exact-staircase law:

* `FullLayerSupply C δ t` — some stack carries `C(n,t)` distinct bad scalars at radius `δ`;
* **`epsMCA_eq_choose_div_of_fullLayerSupply`** — under supply (with floor `t ≥ n/2`
  matching `δ`):  `ε_mca(C, δ) = C(n,t)/q`  **exactly** (LYM above, supply below).

Probe-verified supply instances: `(5,2)` at `δ = 2/5` over `F₁₁`/`F₁₃` (landed exactly in
`MCAWindowInteriorExact.lean`), `(8,3)` at `δ = 1/2` over `p ∈ {1009, 2503, 5003}` —
all strictly inside the window. The two-regime law (issue #357 round-4 comment): supply
holds for `q ≫ C(n,t)²` (collision-free regime) and **must fail below Johnson** (the
literature's `poly(n)/q` bounds), so the layer-attainment boundary is the Johnson radius —
the window is exactly where the LYM ceiling can be tight, and the prize-scale open core is
the collision census of the interpolation-scalar map.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread ProximityGap.MCALYMCeiling

namespace ProximityGap.MCAFullLayerSupply

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Full-layer supply**: some stack carries a full layer's worth (`C(n,t)`) of distinct
bad scalars at radius `δ`. The probe-measurable per-cell hypothesis of the staircase law. -/
def FullLayerSupply (C : Set (ι → A)) (δ : ℝ≥0) (t : ℕ) : Prop :=
  ∃ u : WordStack A (Fin 2) ι, ∃ G : Finset F,
    G.card = (Fintype.card ι).choose t ∧
    ∀ γ ∈ G, mcaEvent (F := F) C δ (u 0) (u 1) γ

/-- **The exact staircase law (conditional).** With floor `t` matching the radius
(`t ≤ (1−δ)·n`, `n ≤ 2t`) and full-layer supply:

  `ε_mca(C, δ) = C(n, t)/q`  exactly —

the LYM ceiling above, the supplied layer below. Every probe-found full-layer stack
instantly pins its cell. -/
theorem epsMCA_eq_choose_div_of_fullLayerSupply (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {t : ℕ}
    (hfloor : (t : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι : ℝ≥0))
    (hhalf : Fintype.card ι ≤ 2 * t)
    (hsupply : FullLayerSupply (F := F) (C : Set (ι → A)) δ t) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = (((Fintype.card ι).choose t : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm (epsMCA_le_choose_div C δ hfloor hhalf) ?_
  obtain ⟨u, G, hGcard, hGbad⟩ := hsupply
  have h := epsMCA_ge_card_div_of_mcaEvent_set (F := F) (A := A)
    (C : Set (ι → A)) δ u G hGbad
  rwa [hGcard] at h

/-- Supply is monotone-meaningful: it forces the field to clear the layer
(`C(n,t) ≤ q`) — the pigeonhole floor of the census regime. -/
theorem card_le_of_fullLayerSupply {C : Set (ι → A)} {δ : ℝ≥0} {t : ℕ}
    (hsupply : FullLayerSupply (F := F) C δ t) :
    (Fintype.card ι).choose t ≤ Fintype.card F := by
  obtain ⟨u, G, hGcard, -⟩ := hsupply
  calc (Fintype.card ι).choose t = G.card := hGcard.symm
    _ ≤ Fintype.card F := by
        simpa using Finset.card_le_univ G

/-! ## Source audit -/

#print axioms epsMCA_eq_choose_div_of_fullLayerSupply
#print axioms card_le_of_fullLayerSupply

end ProximityGap.MCAFullLayerSupply
