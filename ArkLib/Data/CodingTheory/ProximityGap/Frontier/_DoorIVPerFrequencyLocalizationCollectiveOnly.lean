/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceDeficitThicknessInvariant

/-!
# Door IV (Lane 2/3 composition capstone): the WORST-`b` per-frequency decomposition `M = ρ · H`
# has NO thinness-essential lever — BOTH factors are thickness-blind, so the prize content is COLLECTIVE-only

This file is a **composition capstone**. It does NOT introduce a new probe, a new estimate, or a new
mechanism. It conjoins two ALREADY-PROVEN, kernel-checked per-factor rule-3 obstructions from
`_DoorIVCoherenceDeficitThicknessInvariant` into the single citable statement that the DISPROOF_LOG
asserts in prose but no single theorem packaged:

> At the worst frequency `b*`, write the period magnitude as `M(n) = ρ(b*) · H(b*)`, where
> `ρ(b*) = |A + B| / (|A| + |B|)` is the index-2 coset-half COHERENCE and `H(b*) = |A| + |B|` is the
> half-MASS. Both factors were measured THICKNESS-INVARIANT (the coherence deficit `1 − ρ` is
> comparable thin/thick with factor `K ≈ 1.18`; the prize-normalized half-mass is comparable with
> `K ≈ 1.07`). By HARD RULE 3 (thinness-essentiality), a thickness-blind quantity cannot be the
> deciding lever for a bound that is FALSE in the thick window. Hence NEITHER per-frequency factor is
> a thin-specific leak, and the entire prize √-cancellation content lives in the COLLECTIVE BGK
> aggregate over all frequencies — exactly the 25-year-open wall.

## What this is and is NOT

- It IS: a single named theorem conjoining `deficit_lever_not_separating` (coherence factor) and
  `halfMass_lever_not_separating_either_side` (magnitude factor), so the "no per-frequency lever"
  no-go is backed by ONE kernel-checked statement rather than two scattered ones plus prose.
- It is NOT a CORE upper bound, NOT a cancellation/completion/moment/anti-concentration/capacity
  claim, NOT a proof that CORE holds or fails. CORE stays OPEN. This is a refuted-lever constraint
  capstone (the no-fifth-door bookkeeping), in the spirit of `_ShawGrandSynthesis`.

## Honesty scope

The two input theorems carry the empirical comparability constants (`K = 118/100`, `K = 107/100`) as
EXPLICIT hypotheses supplied by the probes; this capstone does NOT re-derive or strengthen them, it
only composes the conclusions. No probe datum is larped as a theorem. Axioms remain
`⊆ {propext, Classical.choice, Quot.sound}` (inherited from the inputs; this file adds none).
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVPerFrequencyLocalizationCollectiveOnly

open ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant
open ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant.RegimeLever

/-- **The two per-frequency factors of `M = ρ · H` at the worst frequency.**

`coherenceDeficit` models the coherence-factor lever `1 − ρ_near(n)` (measured comparable thin/thick
with factor `K ≈ 1.18`); `halfMass` models the magnitude-factor lever `H(b*)/√(n·log)` (measured
comparable with `K ≈ 1.07`). Each is a `RegimeLever`, i.e. a scalar evaluated at matched `n` in the
thin (`β ≈ 4.0`) and thick (`β ≈ 3.05`, CORE-FALSE) regimes. -/
structure WorstBDecomposition where
  /-- The coherence-factor lever (near-worst deficit `1 − ρ_near`). -/
  coherenceDeficit : RegimeLever
  /-- The magnitude-factor lever (prize-normalized half-mass `H/√(n·log)`). -/
  halfMass : RegimeLever

namespace WorstBDecomposition

variable (D : WorstBDecomposition)

/-- **Composition capstone.** Given the two probe-supplied comparability hypotheses — the coherence
deficit comparable with factor `118/100 < 2` (thin side positive) and the half-mass comparable with
factor `107/100 < 2` (both sides positive) — NEITHER per-frequency factor of `M = ρ · H` admits a
factor-2 thin-separation, and the half-mass additionally admits no factor-2 thick-separation.

Reading: every per-`b` factor is thickness-blind, so by rule 3 none can be the thinness-essential
CORE lever; the prize √-cancellation content is therefore COLLECTIVE-only (over all frequencies),
which is precisely the BGK wall. This is the kernel-checked "no per-frequency lever" no-go. -/
theorem no_perFrequency_factor_separates
    (hcoh_thin_pos : 0 < D.coherenceDeficit.thin)
    (hcoh_bound : D.coherenceDeficit.thick ≤ (118 / 100 : ℝ) * D.coherenceDeficit.thin)
    (hhm_thin_pos : 0 < D.halfMass.thin) (hhm_thick_pos : 0 < D.halfMass.thick)
    (hhm_comp : D.halfMass.Comparable (107 / 100 : ℝ)) :
    (¬ D.coherenceDeficit.Factor2ThinSeparation) ∧
      (¬ D.halfMass.Factor2ThinSeparation) ∧
      (¬ D.halfMass.Factor2ThickSeparation) := by
  refine ⟨?_, ?_, ?_⟩
  · -- coherence factor: thickness-invariant ⟹ no factor-2 thin-separation
    exact D.coherenceDeficit.deficit_lever_not_separating hcoh_thin_pos hcoh_bound
  · -- half-mass factor: no factor-2 thin-separation
    exact (D.halfMass.halfMass_lever_not_separating_either_side hhm_thin_pos hhm_thick_pos hhm_comp).1
  · -- half-mass factor: no factor-2 thick-separation (mirror)
    exact (D.halfMass.halfMass_lever_not_separating_either_side hhm_thin_pos hhm_thick_pos hhm_comp).2

/-- **Slogan corollary.** Under the same probe-supplied comparability hypotheses, there is NO
per-frequency factor of `M = ρ · H` that thin-separates: both the coherence factor and the half-mass
factor fail the factor-2 thin-separation a thinness-essential lever would require. (Packages the first
two conjuncts of `no_perFrequency_factor_separates` as the headline "no per-`b` thin lever" statement.) -/
theorem neither_factor_thin_separates
    (hcoh_thin_pos : 0 < D.coherenceDeficit.thin)
    (hcoh_bound : D.coherenceDeficit.thick ≤ (118 / 100 : ℝ) * D.coherenceDeficit.thin)
    (hhm_thin_pos : 0 < D.halfMass.thin) (hhm_thick_pos : 0 < D.halfMass.thick)
    (hhm_comp : D.halfMass.Comparable (107 / 100 : ℝ)) :
    (¬ D.coherenceDeficit.Factor2ThinSeparation) ∧ (¬ D.halfMass.Factor2ThinSeparation) := by
  obtain ⟨h1, h2, _⟩ :=
    D.no_perFrequency_factor_separates hcoh_thin_pos hcoh_bound hhm_thin_pos hhm_thick_pos hhm_comp
  exact ⟨h1, h2⟩

end WorstBDecomposition

end ProximityGap.Frontier.DoorIVPerFrequencyLocalizationCollectiveOnly
