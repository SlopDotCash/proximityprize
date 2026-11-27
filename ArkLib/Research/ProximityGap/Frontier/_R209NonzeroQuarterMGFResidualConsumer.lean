/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R209 nonzero quarter-MGF residual consumer)
-/
import ArkLib.Research.ProximityGap.Frontier._R207NonzeroGaussPeriodDilationConsumer
import ArkLib.Research.ProximityGap.Frontier._wfS11_layercake_moment
import ArkLib.Research.ProximityGap.Frontier._DyadicRawQuarterMGFRefuted
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# R209 (#466): nonzero quarter-MGF residual as an `MGFBound`

R207 isolated the remaining analytic input as the raw sum inequality

```text
Σ_{b≠0} exp((1/4) * ‖η_G(b)‖) ≤ 2 * #(b ≠ 0).
```

The concentration/layer-cake cone already names exactly this shape as
`WFS11.MGFBound s t A c`.  This file repackages the R207 endpoint so the
remaining prize obligation is the single named residual

```text
MGFBound nonzeroFreqs (fun b => ‖η_G(b)‖) 2 (1/4).
```

No analytic estimate is proved here; this is the final interface cleanup before
attacking the MGF/survival bound itself.

**Status: the residual is false at prize scale.**  The score inserted here is the raw modulus
`‖η_G(b)‖`, not the dimensionless `‖η_G(b)‖² / |G|` that the probes test.
`not_nonzeroQuarterMGFResidual` proves `¬ NonzeroQuarterMGFResidual ψ G` for every primitive
`ψ` and every `G` with `128 ≤ |G|` and `2|G| ≤ |F|`, by feeding the Parseval identity
`Σ_{b≠0} ‖η_G(b)‖² = |F||G| − |G|²` into
`DyadicRawQuarterMGFRefuted.not_rawQuarterMGFBound_of_parseval_scale`.  The consumers below are
therefore vacuous on that range; the normalized-square residual of R211/R213 is the live socket
and is not affected.
-/

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The named nonzero quarter-MGF residual for a Gauss-period spectrum.  FALSE whenever
`128 ≤ |G|` and `2|G| ≤ |F|` (`not_nonzeroQuarterMGFResidual`): the score is the raw modulus. -/
def NonzeroQuarterMGFResidual (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  MGFBound (nonzeroFreqs (F := F)) (fun b => ‖eta ψ G b‖) 2 (1 / 4 : ℝ)

/-- **The named residual is false at prize scale.**  For a primitive additive character and any
`G` with `128 ≤ |G|` and `2|G| ≤ |F|`, the raw quarter-MGF budget
`Σ_{b≠0} exp(‖η_G(b)‖/4) ≤ 2(|F| − 1)` fails: `exp(x/4) ≥ x²/32` and Parseval give
`Σ_{b≠0} exp(‖η_G(b)‖/4) ≥ (|F||G| − |G|²)/32 ≥ 2|F|`.  No subgroup structure on `G` is used. -/
theorem not_nonzeroQuarterMGFResidual {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hn : 128 ≤ G.card) (hthin : 2 * G.card ≤ Fintype.card F) :
    ¬ NonzeroQuarterMGFResidual ψ G := by
  intro hMGF
  have hcardF : 1 ≤ Fintype.card F := Fintype.card_pos
  refine ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.not_rawQuarterMGFBound_of_parseval_scale
    (nonzeroFreqs (F := F)) (fun b => ‖eta ψ G b‖) (Fintype.card F : ℝ) (G.card : ℝ)
    (fun b _ => norm_nonneg _) (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hn)
    (by exact_mod_cast hthin) ?_ ?_ hMGF
  · unfold nonzeroFreqs
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Nat.cast_sub hcardF,
      Nat.cast_one]
  · exact ArkLib.ProximityGap.GaussPeriodParsevalFloor.sum_sq_erase_zero hψ G

/-- Unfold the named residual into the raw R207 sum budget. -/
theorem raw_quarter_sum_of_nonzeroQuarterMGFResidual
    {ψ : AddChar F ℂ} {G : Finset F}
    (hMGF : NonzeroQuarterMGFResidual ψ G) :
    (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
      ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ) := by
  exact hMGF

/-- `MGFBound` form of R207's nonzero-frequency dyadic-tail consumer. -/
theorem dyadicTailMGF_of_nonzero_quarterMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (hMGF : NonzeroQuarterMGFResidual ψ G) :
    DyadicTailMGFBound (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) := by
  exact dyadicTailMGF_of_nonzero_gaussPeriod_dilation_quarter ψ G hζ hdisj
    (raw_quarter_sum_of_nonzeroQuarterMGFResidual hMGF)

/-- Prize-square endpoint with the remaining analytic input named as a nonzero
quarter-MGF residual. -/
theorem prize_sq_of_nonzero_quarterMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {Mmax n Q : ℝ} {r : ℕ}
    (hMGF : NonzeroQuarterMGFResidual ψ G)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_nonzero_gaussPeriod_dilation_quarter ψ G hζ hdisj
    (raw_quarter_sum_of_nonzeroQuarterMGFResidual hMGF)
    hMmax hn hQ hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer.raw_quarter_sum_of_nonzeroQuarterMGFResidual
#print axioms ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer.dyadicTailMGF_of_nonzero_quarterMGFResidual
#print axioms ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer.prize_sq_of_nonzero_quarterMGFResidual
#print axioms ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer.not_nonzeroQuarterMGFResidual
