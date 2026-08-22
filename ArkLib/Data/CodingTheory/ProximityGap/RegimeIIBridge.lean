/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAJohnsonCount

/-!
# Regimes (I)+(II) of `InteriorCeiling` modularized onto ONE named line-close bound (#357)

The deployed-prize obligation `InteriorCeiling` ("`ε_mca(C, δ) ≤ ε*` for every `δ` below the
near-capacity KKH26 jump") decomposes into three radius sub-regimes (dossier §13):

* **(I) `[0, half-Johnson]`** — provable via the single-common-center decoder bridge
  (`rs_epsMCA_le_johnson_ceil_of_hwit`);
* **(II) `(half-Johnson, Johnson]`** — the single-center route is *machine-refuted* here
  (`244HwitRefutation`), but the band is still **below Johnson**, where the BCIKS20 / proximity-gap
  correlated-agreement theorem caps the pencil's line-close count by the RS Johnson list size — a
  **known theorem**, not the open prize;
* **(III) `(Johnson, jump)`** — the 25-year beyond-Johnson explicit-RS wall; genuinely open.

This file performs the clean modular wiring for **(I)+(II) together** (everything up to and
including the full Johnson radius). The pivot is the already-proven, *unconditional*
`rs_epsMCA_le_johnson_div_q` (T2): a uniform line-close-count bound `ℓ` at radius `δ` yields
`ε_mca(RS, δ) ≤ ℓ/|F|` with no further hypothesis. Hence the entire sub-Johnson half of
`InteriorCeiling` reduces to a *single named obligation* — a uniform up-to-Johnson line-close bound
`JohnsonLineCloseBound` — discharged in the literature by BCIKS20 correlated agreement. Granting it
(and the trivial cryptographic-field inequality `ℓ/|F| ≤ ε*`, true because `ℓ` is polynomial and
`|F| ≥ 2^128`), `ε_mca(RS, δ) ≤ ε*` for **every** `δ ≤ δ_J`.

Net effect: the irreducibly-open part of the prize shrinks from `[0, jump)` to `(Johnson, jump)`
(regime III only). The hook `JohnsonLineCloseBound` is a *known* result — naming it here is the
project's modularity convention, not a smuggled open conjecture. Regime (III) stays an explicit
named `Prop` elsewhere until literature moves.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped BigOperators NNReal ENNReal
open ProximityGap ProximityGap.MCAGS

namespace ProximityGap.RegimeIIBridge

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

/-- **The sub-Johnson uniform line-close bound** (the BCIKS20 / proximity-gap conclusion, as a
named obligation). For every radius `δ ≤ δ_J` (`δ_J` = the Johnson radius `1 − √ρ`) and every
length-2 pencil `u`, the number of scalars `γ` whose line point `u 0 + γ • u 1` is `δ`-close to the
Reed–Solomon code is at most the fixed polynomial bound `ℓ`. This holds up to the *full* Johnson
radius by correlated agreement — a known theorem — and is the *only* ingredient regimes (I)+(II)
require beyond the already-proven `rs_epsMCA_le_johnson_div_q`. -/
def JohnsonLineCloseBound (domain : ι ↪ F) (k : ℕ) (δJ : ℝ≥0) (ℓ : ℕ) : Prop :=
  ∀ δ : ℝ≥0, δ ≤ δJ → ∀ u : Code.WordStack F (Fin 2) ι,
    (Finset.univ.filter
        (fun γ : F => δᵣ(u 0 + γ • u 1,
          (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card ≤ ℓ

/-- **Regimes (I)+(II) discharge.** Granting the sub-Johnson uniform line-close bound and the
cryptographic-field inequality `ℓ/|F| ≤ ε*`, the prize obligation holds for *every* radius up to
the full Johnson radius: `ε_mca(RS, δ) ≤ ε*` for all `δ ≤ δ_J`. Pure wiring over the unconditional
`rs_epsMCA_le_johnson_div_q`; isolates the open part of `InteriorCeiling` to regime (III). -/
theorem epsMCA_le_of_johnsonLineCloseBound
    {domain : ι ↪ F} {k : ℕ} {δJ : ℝ≥0} {ℓ : ℕ} {εstar : ℝ≥0∞}
    (hJLC : JohnsonLineCloseBound domain k δJ ℓ)
    (hcrypto : (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    ∀ δ : ℝ≥0, δ ≤ δJ →
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ≤ εstar := by
  intro δ hδ
  refine le_trans ?_ hcrypto
  exact rs_epsMCA_le_johnson_div_q (k := k) domain δ ℓ (fun u => hJLC δ hδ u)

/-- **The open core is regime (III) only.** Restated: under the sub-Johnson bound, the *only*
radii at which `ε_mca(RS, δ) ≤ ε*` can still fail are the strictly-above-Johnson ones `δ > δ_J`.
Contrapositive packaging of `epsMCA_le_of_johnsonLineCloseBound` — the precise statement that the
irreducibly-open part of `InteriorCeiling` lives entirely in `(Johnson, jump)`. -/
theorem failure_radius_above_johnson
    {domain : ι ↪ F} {k : ℕ} {δJ : ℝ≥0} {ℓ : ℕ} {εstar : ℝ≥0∞}
    (hJLC : JohnsonLineCloseBound domain k δJ ℓ)
    (hcrypto : (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    {δ : ℝ≥0}
    (hfail : ¬ epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ≤ εstar) :
    δJ < δ := by
  by_contra hle
  exact hfail (epsMCA_le_of_johnsonLineCloseBound hJLC hcrypto δ (not_lt.mp hle))

end ProximityGap.RegimeIIBridge

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.RegimeIIBridge.epsMCA_le_of_johnsonLineCloseBound
#print axioms ProximityGap.RegimeIIBridge.failure_radius_above_johnson
