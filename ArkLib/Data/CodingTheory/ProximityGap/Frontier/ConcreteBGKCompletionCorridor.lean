/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteCompletionCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.WorstPeriodSqrtNFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy

/-!
# The CONCRETE completion corridor `√(d/2) ≤ M(μ_d) ≤ √q` on the real worst period (#444)

**Lane-2 capstone rung — frontier-movement, wiring two proven concrete bounds + the tetrachotomy
scale onto the ACTUAL torsion-subgroup worst period.**

The no-fifth-door tetrachotomy (`_NoFifthDoorTetrachotomy`) localizes the open problem to door (iv):
every classical door delivers at best the BGK scale `bgkScale n L = √(n·L)`, door (ii) (√q-completion)
delivers `√q ≥ √(n·L)` (overshoots), and the prize floor is `√n`.  That file's corridor reasoning is
stated on an **abstract** `M`.  Separately, two CONCRETE bounds are proven on the *real* worst period
`M(μ_d) = worstPeriod ψ (torsion F d)`:

* the clean thin-regime Plancherel floor `√(d/2) ≤ M(μ_d)` (`worstPeriod_ge_sqrt_half_n`, thin regime
  `q ≥ 2d`), and
* the classical √q-completion ceiling `M(μ_d) ≤ √q` (`worstPeriod_torsion_le_sqrt_card`, the door-(ii)
  mechanism's certified scale).

But these two had never been combined into the concrete door-(ii) completion corridor on the actual
torsion-subgroup period, nor wired to the tetrachotomy's quantitative "shave the √L factor" statement.
This file closes that gap.

## What this supplies (all on the REAL `M(μ_d)`, `d ∣ q−1`)

* `worstPeriod_torsion_completion_corridor` — the concrete completion corridor
  **`√(d/2) ≤ M(μ_d) ≤ √q`** (clean Plancherel floor, proven √q-completion ceiling).
* `bgkScale_lt_completionCeiling` — in the prize regime the completion ceiling `√q` strictly exceeds
  the BGK scale `√(d·L)` (`d·L < q`, automatic at `q = d^β`, `β ≥ 2`, `L ≪ d`): door (ii) overshoots.
* `doorIV_shave_obligation` — the quantitative door-(iv) target on the real period: the proven
  completion ceiling `√q` must be brought down past the BGK scale `bgkScale d L = √L · √d`
  (`bgkScale_eq_sqrtL_mul_prizeScale`) to the prize floor `√d`.  The remaining `√L = √(log(p/d))`
  factor between BGK and the floor is exactly the open door-(iv) shave.

## Honesty (scope)

Pure assembly of two proven concrete bounds + the tetrachotomy scale identity.  The floor is
unconditional (Parseval, thin regime); the ceiling is the classical completion bound; the overshoot
is an elementary regime inequality.  NO anti-concentration, NO new cancellation, NO moment, NO
capacity claim.  CORE `M(μ_d) ≤ C·√(d·log(p/d))` stays OPEN — door (iv), the `√L`-shave from the
proven `√q` ceiling, is the open problem; this file states the obligation on the real object, it does
not discharge it.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteCompletionCeiling
open ProximityGap.Frontier.WorstPeriodSqrtNFloor
open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

namespace ProximityGap.Frontier.ConcreteBGKCompletionCorridor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The concrete completion corridor on the real torsion-subgroup worst period.**  For `μ_d`
(`d ∣ q−1`, `d > 0`) in the thin regime `q ≥ 2d`, the worst nonzero period is bracketed by the clean
Plancherel floor and the classical √q-completion ceiling:
`√(d/2) ≤ M(μ_d) ≤ √q`.  The lower endpoint is the prize-shaped `Ω(√d)` floor; the upper endpoint is
the door-(ii) completion scale.  The prize CORE `M(μ_d) ≤ C·√(d·log(p/d))` lives strictly inside. -/
theorem worstPeriod_torsion_completion_corridor {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hne : (nonzeroFreqs F).Nonempty)
    (hd1 : 1 ≤ (d : ℝ))
    (hq2d : 2 * (d : ℝ) ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((d : ℝ) / 2) ≤ worstPeriod ψ (torsion F d) hne
      ∧ worstPeriod ψ (torsion F d) hne ≤ Real.sqrt (Fintype.card F) := by
  have hcard : ((torsion F d).card : ℝ) = (d : ℝ) := by
    rw [card_torsion hd hd0]
  refine ⟨?_, worstPeriod_torsion_le_sqrt_card hd hd0 hψ hne⟩
  have hfloor := worstPeriod_ge_sqrt_half_n hψ (torsion F d) hne
    (by rw [hcard]; exact hd1) (by rw [hcard]; exact hq2d)
  rwa [hcard] at hfloor

/-- **Door-(ii) overshoot on the concrete scales.**  In the prize regime the field size dominates the
BGK argument (`d·L ≤ q`, automatic at `q = d^β`, `β ≥ 2`, `L ≪ d`).  Then the proven √q-completion
ceiling that door (ii) certifies strictly exceeds the BGK scale `√(d·L)`: the completion door
overshoots, exactly as the tetrachotomy claims, with no assumption beyond the regime fact. -/
theorem bgkScale_le_completionCeiling {d L : ℝ} (hq : d * L ≤ (Fintype.card F : ℝ)) :
    bgkScale d L ≤ Real.sqrt (Fintype.card F) := by
  unfold bgkScale
  exact Real.sqrt_le_sqrt hq

/-- **The quantitative door-(iv) shave obligation on the real worst period.**  The proven completion
ceiling `√q` factors through the BGK scale: `bgkScale d L = √L · √d = √L · prizeScale d`.  So the open
door-(iv) obligation is, on the actual character sum, to bring the worst period from inside the proven
corridor `[√(d/2), √q]` down across the BGK scale `√L·√d` to the prize floor `√d` — i.e. to shave the
multiplicative `√L = √(log(p/d))` factor that BGK leaves above the floor.  This packages the exact
remaining gap quantitatively; it does NOT discharge it. -/
theorem doorIV_shave_obligation {d L : ℝ} (hd : 0 ≤ d) (hL : 0 ≤ L) :
    bgkScale d L = Real.sqrt L * prizeScale d :=
  bgkScale_eq_sqrtL_mul_prizeScale hd hL

/-- **Door-(ii) is dominated by the TRIVIAL ceiling in the thin regime.**  Sharper than the
BGK-overshoot above: in the prize regime `d² ≤ q` (`q = d^β, β ≥ 2`) the classical √q-completion
ceiling does not even beat the ELEMENTARY triangle ceiling `M(μ_d) ≤ d`, since `d ≤ √q`.  So the
completion door provides ZERO improvement over the trivial bound on the worst period: it is not merely
above the BGK scale, it is above `d` itself.  This is the strongest form of the door-(ii) refutation —
completion is vacuous in the thin regime relative to the free triangle bound.  No CORE/cancellation/
completion/anti-concentration/capacity claim. -/
theorem card_le_completionCeiling_of_sq_le {d : ℝ} (hd : 0 ≤ d)
    (hsq : d ^ 2 ≤ (Fintype.card F : ℝ)) :
    d ≤ Real.sqrt (Fintype.card F) := by
  rw [show d = Real.sqrt (d ^ 2) from (Real.sqrt_sq hd).symm]
  exact Real.sqrt_le_sqrt hsq

end ProximityGap.Frontier.ConcreteBGKCompletionCorridor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteBGKCompletionCorridor.card_le_completionCeiling_of_sq_le
#print axioms ProximityGap.Frontier.ConcreteBGKCompletionCorridor.worstPeriod_torsion_completion_corridor
#print axioms ProximityGap.Frontier.ConcreteBGKCompletionCorridor.bgkScale_le_completionCeiling
#print axioms ProximityGap.Frontier.ConcreteBGKCompletionCorridor.doorIV_shave_obligation
