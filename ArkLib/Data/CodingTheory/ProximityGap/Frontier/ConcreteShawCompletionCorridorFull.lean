/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawCompletionCorridor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawValueThinFloor

/-!
# The COMPLETE concrete Shaw completion corridor `1/√(2L) ≤ Sh(M(μ_d)) ≤ √(q/(d·L))` (#444)

**Lane-2 capstone rung — frontier-movement, the tightest concrete normalized corridor on the REAL
torsion-subgroup worst period, both endpoints.**

Two existing concrete Shaw-value rungs each give ONE side on the real torsion-subgroup worst period
`M(μ_d) = worstPeriod ψ (torsion F d)` (`d ∣ q−1`):

* `ConcreteShawCompletionCorridor.shawValue_worstPeriod_torsion_le_sqrt_card` — the TIGHT SOTA ceiling
  `Sh(M(μ_d)) ≤ √q / scale`, the √q-completion baseline normalized; and
* `ConcreteShawValueThinFloor.shawValue_worstPeriod_floor_clean` — the clean thin-regime floor
  `1/√(2L) ≤ Sh(M(μ_d))` (valid `q ≥ 2d`).

But they were stated on different objects (the floor on a generic `G`, the ceiling on `torsion F d`)
and never combined into the single two-sided concrete Shaw corridor on `μ_d`.  This file specializes
the clean floor to `torsion F d` (via `card_torsion`) and pairs it with the SOTA ceiling, giving the
tightest normalized corridor the campaign has on the real object:

> `1/√(2L) ≤ Sh(M(μ_d)) ≤ √(q/(d·L))`.

The lower endpoint is the `n`-independent Plancherel floor `1/√(2·log(p/d))`; the upper endpoint is the
SOTA √q-completion baseline `√(q/(d·L)) = d^{(β−1)/2}/√L` (at `q = d^β`).  The prize CORE
`Sh(M(μ_d)) = O(1)` lives strictly inside; collapsing the upper SOTA endpoint to an absolute constant
IS the prize.

## What this supplies (all on the REAL `M(μ_d)`)

* `ceiling_sqrt_card_eq` — closed form of the SOTA ceiling endpoint: `√q / scale = √(q/(d·L))`.
* `shawValue_worstPeriod_torsion_clean_floor` — the clean floor `1/√(2L) ≤ Sh(M(μ_d))` on `μ_d`.
* `shawValue_worstPeriod_torsion_full_corridor` — the complete two-sided corridor
  `1/√(2L) ≤ Sh(M(μ_d)) ≤ √(q/(d·L))`.

## Honesty (scope)

Pure assembly of two proven concrete Shaw-value bounds + one closed-form simplification.  The floor is
unconditional (Parseval, thin regime `q ≥ 2d`); the ceiling is the classical √q-completion baseline.
NO anti-concentration, NO new cancellation, NO moment, NO capacity claim.  CORE `Sh(M(μ_d)) = O(1)`
stays OPEN; this records the tightest concrete normalized starting line, both endpoints, on the real
character sum.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteShawCompletionCorridor
open ProximityGap.Frontier.ConcreteShawValueThinFloor

namespace ProximityGap.Frontier.ConcreteShawCompletionCorridorFull

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Closed form of the SOTA ceiling endpoint.**  `√q / √(d·L) = √(q/(d·L))`.  The √q-completion
baseline, normalized by the Shaw scale `√(d·L)`, is `√(q/(d·L))` — at `q = d^β` this is
`d^{(β−1)/2}/√L`, the concrete SOTA starting line above the prize target. -/
theorem ceiling_sqrt_card_eq {d L q : ℝ} (hd : 0 < d) (hL : 0 < L) (hq : 0 ≤ q) :
    Real.sqrt q / prizeScale d L = Real.sqrt (q / (d * L)) := by
  unfold prizeScale
  rw [Real.sqrt_div hq]

/-- **The clean thin-regime Shaw floor on the real torsion-subgroup worst period.**  Specializes
`shawValue_worstPeriod_floor_clean` to `μ_d = torsion F d` (`card (torsion F d) = d`): in the thin
regime `q ≥ 2d`, `1/√(2L) ≤ Sh(M(μ_d))`. -/
theorem shawValue_worstPeriod_torsion_clean_floor {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hne : (nonzeroFreqs F).Nonempty)
    (hd1 : 1 ≤ (d : ℝ))
    (hq2d : 2 * (d : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale ((torsion F d).card : ℝ) L) :
    1 / Real.sqrt (2 * L)
      ≤ shawValue (worstPeriod ψ (torsion F d) hne) ((torsion F d).card : ℝ) L := by
  have hcard : ((torsion F d).card : ℝ) = (d : ℝ) := by rw [card_torsion hd hd0]
  exact shawValue_worstPeriod_floor_clean hψ (torsion F d) hne
    (by rw [hcard]; exact hd1) (by rw [hcard]; exact hq2d) hs

/-- **The COMPLETE concrete Shaw completion corridor on the real torsion-subgroup worst period.**
`1/√(2L) ≤ Sh(M(μ_d)) ≤ √(q/(d·L))`.  Lower endpoint: the `n`-independent thin-regime Plancherel
floor (clean, unconditional at `q ≥ 2d`).  Upper endpoint: the SOTA √q-completion baseline
`√(q/(d·L)) = d^{(β−1)/2}/√L`.  The prize target `Sh(M(μ_d)) = O(1)` lives strictly inside this proven
corridor — collapsing the SOTA upper endpoint to an absolute constant IS the prize. -/
theorem shawValue_worstPeriod_torsion_full_corridor {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hne : (nonzeroFreqs F).Nonempty)
    (hd1 : 1 ≤ (d : ℝ))
    (hq2d : 2 * (d : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L)
    (hs : 0 < prizeScale ((torsion F d).card : ℝ) L) :
    1 / Real.sqrt (2 * L)
        ≤ shawValue (worstPeriod ψ (torsion F d) hne) ((torsion F d).card : ℝ) L
      ∧ shawValue (worstPeriod ψ (torsion F d) hne) ((torsion F d).card : ℝ) L
          ≤ Real.sqrt ((Fintype.card F : ℝ) / ((d : ℝ) * L)) := by
  have hcard : ((torsion F d).card : ℝ) = (d : ℝ) := by rw [card_torsion hd hd0]
  have hqpos : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  refine ⟨shawValue_worstPeriod_torsion_clean_floor hd hd0 hψ hne hd1 hq2d hs, ?_⟩
  have hceil := shawValue_worstPeriod_torsion_le_sqrt_card hd hd0 hψ hne hs
  rw [hcard] at hceil ⊢
  rwa [ceiling_sqrt_card_eq (lt_of_lt_of_le one_pos hd1) hL hqpos] at hceil

/-- **The SHARP thin-regime floor on the canonical prize object `μ_d`.**  On the actual torsion
subgroup `μ_d = torsion F d` (`card = d`), in the prize regime `d² ≤ q` (`q = d^β, β ≥ 2`), the
worst period satisfies `√(d − 1) ≤ M(μ_d)` — the sharp quadratic-regime Parseval floor specialized
to the exact prize object.  This is strictly stronger than the clean `1/√(2L)`-normalized floor
(`shawValue_worstPeriod_torsion_clean_floor`), which only reaches a constant fraction: here the floor
is at its TRUE value `√d`.  Still the LOWER/Johnson side only — the gap to the BGK upper
`C·√(d·log(q/d))` is exactly the open prize. -/
theorem worstPeriod_torsion_sharp_floor {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hne : (nonzeroFreqs F).Nonempty)
    (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) (hd1 : (1 : ℝ) < (d : ℝ))
    (hsq : (d : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((d : ℝ) - 1) ≤ worstPeriod ψ (torsion F d) hne := by
  have hcard : ((torsion F d).card : ℝ) = (d : ℝ) := by rw [card_torsion hd hd0]
  have hbase := ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_card_pred_of_sq_le
    hψ (torsion F d) hne hq1 (by rw [hcard]; exact hd1) (by rw [hcard]; exact hsq)
  rwa [hcard] at hbase

end ProximityGap.Frontier.ConcreteShawCompletionCorridorFull

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.worstPeriod_torsion_sharp_floor
#print axioms ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.ceiling_sqrt_card_eq
#print axioms ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.shawValue_worstPeriod_torsion_clean_floor
#print axioms ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.shawValue_worstPeriod_torsion_full_corridor
